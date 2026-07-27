/-
  EvmAsm.Codegen.Programs.SystemCallStoragePreload

  `stage_predeploy_storage_preload` (bead evm-asm-8uld3.2.1.4, EIP-7002/7251) — build the
  (key, original-value) storage preload for a system-call predeploy, so its SLOAD of the
  request queue reads the real witness values during the system call (8uld3.2.1.3 compose).

  Composes the existing primitives:
    * bal_recipient_storage_keys (BlockVerdictContractStorage) — enumerate the predeploy's
      accessed slot keys from its BAL AccountChanges entry (cap 512).
    * slot_at_header_state_root (StateCompose) — for each key, walk the witness MPT
      (header.state_root -> account leaf -> storage trie -> slot) to the ORIGINAL pre-block
      value; the 32-byte u256 lands in the `sahsr_u256` global (a0 = status, nonzero = fail).

  Witness/header args are passed via the `sps_*` globals (set by the caller / the 8uld3.2.2
  verdict wiring), keeping the function within a0-a2. Output = count x 64-byte (key:32,
  value:32) pairs for stage_runtime_payload_code's a5/a6 preload; on a lookup failure the
  value is written 0 (conservative). bal_find_account_by_address (which yields the
  AccountChanges ptr, with the length derived from the RLP item header) is the caller's step.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.StateCompose
import EvmAsm.Codegen.Programs.BlockVerdictContractStorage
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_predeploy_storage_preload
    a0 = predeploy AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out ptr (count x 64-byte (key:32 BE, value:32 BE) pairs; caller buffer >=
         bsrAccountSlotCap*64)
    Globals (caller-set): sps_addr (20-byte predeploy address), sps_header / sps_header_len,
      sps_state / sps_state_len, sps_storage / sps_storage_len.
    Returns a0 = slot count (0 on parse failure; if > bsrAccountSlotCap — or if any slot
    carries > bsrMaxTuplesPerSlot change tuples — nothing/partial-keys-only written and a
    count > bsrAccountSlotCap returned so the caller MUST bail conservatively — staging a
    count the buffer doesn't hold reads garbage past c1_preload. fhsxz.2.4.2.66.1 raised
    the cap 128 -> 512 for the 306-change system_contract_errors predeploys;
    fhsxz.2.4.2.66.1.2 made it gas-derived: a 200M block's user txs can legitimately put
    thousands of changes+reads on a predeploy, so the only non-rejecting bound is the
    BAL-item budget itself). -/
def stagePredeployStoragePreloadFunction : String :=
  "stage_predeploy_storage_preload:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a2                    # out ptr\n" ++
  "  mv s5, a0                    # AccountChanges ptr (kept for the reads pass)\n" ++
  "  mv s6, a1                    # AccountChanges len\n" ++
  -- bal_recipient_storage_keys(AccountChanges, len, sps_keys) -> changes-slot count
  "  la a2, sps_keys\n" ++
  "  jal ra, bal_recipient_storage_keys\n" ++
  "  mv s1, a0                    # changes-slot count\n" ++
  "  li t0, " ++ toString bsrAccountSlotCap ++ "\n  bgtu s1, t0, .Lspsp_done\n" ++   -- >cap changes: bail (write nothing, return count)
  -- 8uld3.2.3.3.1 Fix2: ALSO stage the predeploy's storage_READS (AccountChanges item 2).
  -- A no-requests predeploy reads the queue head/tail/count slots it never writes, so a
  -- changes-only preload leaves those SLOADs reading garbage (the e0010046 unmapped-read
  -- crash). Append the reads keys after the changes keys; the loop below stages a real
  -- pre-block value for each. (a0/a1 were clobbered by the changes call; restore from s5/s6.)
  "  mv a0, s5; mv a1, s6\n" ++
  "  slli t0, s1, 5; la t1, sps_keys; add a2, t1, t0   # &sps_keys[changes_count]\n" ++
  "  li t0, " ++ toString bsrAccountSlotCap ++ "; sub a3, t0, s1                         # remaining capacity\n" ++
  "  jal ra, bal_recipient_storage_reads_keys\n" ++
  "  add s1, s1, a0                                     # total = changes + reads\n" ++
  "  li t0, " ++ toString bsrAccountSlotCap ++ "\n  bgtu s1, t0, .Lspsp_done\n" ++   -- combined >cap: bail
  -- Fix6 pre-pass: sps_sysidx = MAX block_access_index across the predeploy's changed slots.
  -- The block-end system call is the last writer, so its index is this max; a slot's pre-system
  -- value (what the predeploy reads) is the last change tuple with index < sps_sysidx.
  "  la t0, sps_sysidx; sd zero, 0(t0)\n" ++
  "  li s2, 0\n" ++
  ".Lspsp_pre:\n" ++
  "  beq s2, s1, .Lspsp_pred\n" ++
  "  slli t0, s2, 5; la t1, sps_keys; add a2, t1, t0\n" ++
  "  mv a0, s5; mv a1, s6; la a3, sps_tuples\n" ++
  "  jal ra, bal_slot_tuple_sequence\n" ++
  -- .66.1.2: > bsrMaxTuplesPerSlot tuples -> the helper wrote nothing; bail conservatively
  -- (force a count the caller's cap check rejects) instead of scanning stale sps_tuples.
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu a0, t0, .Lspsp_toobig\n" ++
  "  li t0, 0\n" ++
  ".Lspsp_premax:\n" ++
  "  beq t0, a0, .Lspsp_premaxd\n" ++
  "  slli t1, t0, 5; slli t6, t0, 3; add t1, t1, t6; la t2, sps_tuples; add t2, t2, t1\n" ++
  "  ld t3, 0(t2); la t4, sps_sysidx; ld t5, 0(t4); bleu t3, t5, .Lspsp_prenext\n" ++
  "  sd t3, 0(t4)\n" ++
  ".Lspsp_prenext:\n" ++
  "  addi t0, t0, 1; j .Lspsp_premax\n" ++
  ".Lspsp_premaxd:\n" ++
  "  addi s2, s2, 1; j .Lspsp_pre\n" ++
  ".Lspsp_pred:\n" ++
  "  li s2, 0                     # i\n" ++
  ".Lspsp_loop:\n" ++
  "  beq s2, s1, .Lspsp_done\n" ++
  "  slli t0, s2, 5; la t1, sps_keys; add s3, t1, t0   # s3 = &key[i] (32B)\n" ++
  "  slli t0, s2, 6; add s4, s0, t0                     # s4 = &out[i] (64B stride)\n" ++
  -- 8uld3.2.3.3.1 Fix5: write the preload KEY byte-reversed (BE->LE: dst[31-i]<-src[i]) so the
  -- dispatcher's SLOAD (little-endian-limb stack key) matches. sps_keys stays BE for the MPT
  -- lookup (a3) below. Without this, non-zero queue slots were invisible (SLOAD miss -> 0), so a
  -- non-empty queue derived an EMPTY body -> requests_hash mismatch. Same BE->LE class as #8694.
  "  li t0, 0\n" ++
  ".Lspsp_krev:\n" ++
  "  li t1, 32; beq t0, t1, .Lspsp_krevd\n" ++
  "  add t2, s3, t0; lbu t3, 0(t2); li t4, 31; sub t4, t4, t0; add t4, s4, t4; sb t3, 0(t4); addi t0, t0, 1; j .Lspsp_krev\n" ++
  ".Lspsp_krevd:\n" ++
  -- 8uld3.2.3.3.1 Fix6: the system call runs at block END (it is the LAST writer of these slots,
  -- so its block_access_index is the MAX across the predeploy's changes — empirically the 7002
  -- reset lands at the max index, e.g. (idx 1, val 1) then (idx 2, val 0)). The value the predeploy
  -- READS for a slot = the last BAL storage_changes tuple with index < the system index (sps_sysidx,
  -- = that global max, computed in the pre-pass above). Fall back to the pre-block MPT value when a
  -- slot has no pre-system change (only system-written: queue head/excess read pre-state).
  "  mv a0, s5; mv a1, s6; mv a2, s3; la a3, sps_tuples\n" ++
  "  jal ra, bal_slot_tuple_sequence\n" ++         -- a0 = tuple count (0 if slot absent)
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu a0, t0, .Lspsp_toobig\n" ++   -- .66.1.2: helper wrote nothing -> bail
  "  li t0, 0\n" ++                                 -- j
  "  li t5, 0\n" ++                                 -- found new_value ptr (0 = none)
  "  la t4, sps_sysidx; ld t4, 0(t4)\n" ++          -- t4 = system-call index (global max)
  ".Lspsp_tscan:\n" ++
  "  beq t0, a0, .Lspsp_tscand\n" ++
  "  slli t1, t0, 5; slli t6, t0, 3; add t1, t1, t6; la t2, sps_tuples; add t2, t2, t1\n" ++   -- &rec[j] (40B)
  "  ld t3, 0(t2); bgeu t3, t4, .Lspsp_tnext\n" ++  -- skip the system write (index >= sysidx)
  "  addi t5, t2, 8\n" ++                           -- found = &new_value (last pre-system write wins)
  ".Lspsp_tnext:\n" ++
  "  addi t0, t0, 1; j .Lspsp_tscan\n" ++
  ".Lspsp_tscand:\n" ++
  "  beqz t5, .Lspsp_mptval\n" ++                   -- no regular-tx change -> pre-block MPT value
  "  li t0, 0\n" ++                                 -- reverse found new_value (32B BE) -> out[i][32:64] LE
  ".Lspsp_tvrev:\n" ++
  "  li t1, 32; beq t0, t1, .Lspsp_tvrevd\n" ++
  "  add t2, t5, t0; lbu t3, 0(t2); li t4, 63; sub t4, t4, t0; add t4, s4, t4; sb t3, 0(t4); addi t0, t0, 1; j .Lspsp_tvrev\n" ++
  ".Lspsp_tvrevd:\n" ++
  "  j .Lspsp_next\n" ++
  ".Lspsp_mptval:\n" ++
  -- slot_at_header_state_root(header, header_len, predeploy_addr, &key[i], state, state_len, storage, storage_len)
  "  la t0, sps_header; ld a0, 0(t0)\n" ++
  "  la t0, sps_header_len; ld a1, 0(t0)\n" ++
  "  la a2, sps_addr\n" ++
  "  mv a3, s3\n" ++                              -- slot_idx = key[i] (32B BE)
  "  la t0, sps_state; ld a4, 0(t0)\n" ++
  "  la t0, sps_state_len; ld a5, 0(t0)\n" ++
  "  la t0, sps_storage; ld a6, 0(t0)\n" ++
  "  la t0, sps_storage_len; ld a7, 0(t0)\n" ++
  "  jal ra, slot_at_header_state_root\n" ++
  "  bnez a0, .Lspsp_zero\n" ++                   -- lookup failed -> value 0 (conservative)
  -- Fix5: value BE->LE reversed into out[i][32..64] (dst[63-i]<-src[i]).
  "  la t5, sahsr_u256; li t0, 0\n" ++
  ".Lspsp_vrev:\n" ++
  "  li t1, 32; beq t0, t1, .Lspsp_vrevd\n" ++
  "  add t2, t5, t0; lbu t3, 0(t2); li t4, 63; sub t4, t4, t0; add t4, s4, t4; sb t3, 0(t4); addi t0, t0, 1; j .Lspsp_vrev\n" ++
  ".Lspsp_vrevd:\n" ++
  "  j .Lspsp_next\n" ++
  ".Lspsp_zero:\n" ++
  "  addi t2, s4, 32; sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)\n" ++
  ".Lspsp_next:\n" ++
  "  addi s2, s2, 1\n  j .Lspsp_loop\n" ++
  -- .66.1.2: per-slot tuple overflow -> return a count above bsrAccountSlotCap so every
  -- caller's existing `bgtu a0, cap` check routes to its conservative bail.
  ".Lspsp_toobig:\n" ++
  "  li s1, " ++ toString (bsrAccountSlotCap + 1) ++ "\n" ++
  ".Lspsp_done:\n" ++
  "  mv a0, s1\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- Globals for `stage_predeploy_storage_preload` (caller-set witness/header pointers +
    the predeploy address + the slot-key scratch buffer). -/
def stagePredeployStoragePreloadData : String :=
  ".balign 8\n" ++
  "sps_keys:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++      -- bsrAccountSlotCap x 32-byte slot keys (.66.1.2: gas-derived, was 512)
  ".balign 8\n" ++
  "sps_tuples:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++    -- Fix6: bsrMaxTuplesPerSlot x 40-byte (block_access_index, new_value) tuples per slot (.66.1.2)
  "sps_sysidx:\n  .zero 8\n" ++        -- Fix6: system-call block_access_index (= max change index)
  ".balign 8\n" ++
  "sps_addr:\n  .zero 32\n" ++         -- predeploy address (20B, padded)
  "sps_header:\n  .zero 8\n" ++
  "sps_header_len:\n  .zero 8\n" ++
  "sps_state:\n  .zero 8\n" ++
  "sps_state_len:\n  .zero 8\n" ++
  "sps_storage:\n  .zero 8\n" ++
  "sps_storage_len:\n  .zero 8\n"

/-- `zisk_stage_predeploy_storage_preload`: probe. Reuses the bal probe's hand-encoded
    AccountChanges (brsk_acct: one slot key 0x00..07) + a NULL witness (sps_* default 0),
    so slot_at_header_state_root fails and values are 0. Verifies the key enumeration +
    (key,value) pairing; the real MPT value-lookup is verified by the 8uld3.2.2 wiring.
    Output: +0 count (expect 1); +8 key byte31 (expect 0x00 — Fix5 writes the key
    BE->LE-reversed, so the BE key 0x00..07 has 0x07 at byte 0); +16 value byte0
    (expect 0); +24 key byte0 (expect 0x07). -/
def ziskStagePredeployStoragePreloadPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, brsk_acct\n  li a1, 63\n  la a2, spsp_out\n" ++
  "  jal ra, stage_predeploy_storage_preload\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++                          -- count
  "  la t1, spsp_out\n" ++
  "  lbu t2, 31(t1); sd t2, 8(t0)\n" ++          -- key[0] byte 31 (expect 0x07)
  "  lbu t2, 32(t1); sd t2, 16(t0)\n" ++         -- value[0] byte 0 (expect 0; null witness)
  "  lbu t2, 0(t1); sd t2, 24(t0)\n" ++          -- key[0] byte 0 (expect 0x00 left-pad)
  "  j .Lspspp_done\n" ++
  stagePredeployStoragePreloadFunction ++ "\n" ++
  balRecipientStorageKeysFunction ++ "\n" ++
  -- 8uld3 Fix2/Fix6 added these calls to the preload; the probe must link them too
  -- (pre-existing link failure fixed alongside .66.1.2).
  balRecipientStorageReadsKeysFunction ++ "\n" ++
  balSlotTupleSequenceFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  -- slot_at_header_state_root + its MPT deps (rlpListNthItem is in this set):
  zkvmKeccak256Function ++ "\n" ++
  witnessLookupByHashFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  mptNodeKindFunction ++ "\n" ++
  mptBranchChildFunction ++ "\n" ++
  hpDecodeNibblesFunction ++ "\n" ++
  bytesToNibblesFunction ++ "\n" ++
  mptWalkFunction ++ "\n" ++
  mptLookupByKeyFunction ++ "\n" ++
  accountDecodeFunction ++ "\n" ++
  accountAtAddressFunction ++ "\n" ++
  slotDecodeU256Function ++ "\n" ++
  slotAtIndexFunction ++ "\n" ++
  headerExtractStateRootFunction ++ "\n" ++
  slotAtHeaderStateRootFunction ++ "\n" ++
  ".Lspspp_done:"

def ziskStagePredeployStoragePreloadDataSection : String :=
  ziskBalRecipientStorageKeysDataSection ++ "\n" ++   -- brsk_* scratch + brsk_acct fixture
  ziskSlotAtHeaderStateRootDataSection ++ "\n" ++     -- slot MPT scratch + sahsr_u256
  balSlotTupleSequenceData ++ "\n" ++                  -- bts_* scratch (Fix6 tuple pre-pass)
  ziskRlpFieldToU64DataSection ++ "\n" ++              -- rfu_* scratch for rlp_field_to_u64
  stagePredeployStoragePreloadData ++ "\n" ++          -- sps_* (null witness by default)
  ".balign 8\n" ++
  "spsp_out:\n  .zero 8256\n"

def ziskStagePredeployStoragePreloadProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStagePredeployStoragePreloadPrologue
  dataAsm     := ziskStagePredeployStoragePreloadDataSection
}

end EvmAsm.Codegen
