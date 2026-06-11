/-
  EvmAsm.Codegen.Programs.SystemCallStoragePreload

  `stage_predeploy_storage_preload` (bead evm-asm-8uld3.2.1.4, EIP-7002/7251) — build the
  (key, original-value) storage preload for a system-call predeploy, so its SLOAD of the
  request queue reads the real witness values during the system call (8uld3.2.1.3 compose).

  Composes the existing primitives:
    * bal_recipient_storage_keys (BlockVerdictContractStorage) — enumerate the predeploy's
      accessed slot keys from its BAL AccountChanges entry (cap 128).
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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## stage_predeploy_storage_preload
    a0 = predeploy AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = out ptr (count x 64-byte (key:32 BE, value:32 BE) pairs; caller buffer >= 128*64)
    Globals (caller-set): sps_addr (20-byte predeploy address), sps_header / sps_header_len,
      sps_state / sps_state_len, sps_storage / sps_storage_len.
    Returns a0 = slot count (0 on parse failure; if > 128, nothing written, true count
    returned so the caller bails conservatively). -/
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
  "  li t0, 128\n  bgtu s1, t0, .Lspsp_done\n" ++   -- >128 changes: bail (write nothing, return count)
  -- 8uld3.2.3.3.1 Fix2: ALSO stage the predeploy's storage_READS (AccountChanges item 2).
  -- A no-requests predeploy reads the queue head/tail/count slots it never writes, so a
  -- changes-only preload leaves those SLOADs reading garbage (the e0010046 unmapped-read
  -- crash). Append the reads keys after the changes keys; the loop below stages a real
  -- pre-block value for each. (a0/a1 were clobbered by the changes call; restore from s5/s6.)
  "  mv a0, s5; mv a1, s6\n" ++
  "  slli t0, s1, 5; la t1, sps_keys; add a2, t1, t0   # &sps_keys[changes_count]\n" ++
  "  li t0, 128; sub a3, t0, s1                         # remaining capacity\n" ++
  "  jal ra, bal_recipient_storage_reads_keys\n" ++
  "  add s1, s1, a0                                     # total = changes + reads\n" ++
  "  li t0, 128\n  bgtu s1, t0, .Lspsp_done\n" ++   -- combined >128: bail
  "  li s2, 0                     # i\n" ++
  ".Lspsp_loop:\n" ++
  "  beq s2, s1, .Lspsp_done\n" ++
  "  slli t0, s2, 5; la t1, sps_keys; add s3, t1, t0   # s3 = &key[i] (32B)\n" ++
  "  slli t0, s2, 6; add s4, s0, t0                     # s4 = &out[i] (64B stride)\n" ++
  -- copy key (32B) -> out[i][0..32]
  "  ld a5, 0(s3); sd a5, 0(s4); ld a5, 8(s3); sd a5, 8(s4)\n" ++
  "  ld a5, 16(s3); sd a5, 16(s4); ld a5, 24(s3); sd a5, 24(s4)\n" ++
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
  "  la t1, sahsr_u256; addi t2, s4, 32\n" ++
  "  ld a5, 0(t1); sd a5, 0(t2); ld a5, 8(t1); sd a5, 8(t2)\n" ++
  "  ld a5, 16(t1); sd a5, 16(t2); ld a5, 24(t1); sd a5, 24(t2)\n" ++
  "  j .Lspsp_next\n" ++
  ".Lspsp_zero:\n" ++
  "  addi t2, s4, 32; sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)\n" ++
  ".Lspsp_next:\n" ++
  "  addi s2, s2, 1\n  j .Lspsp_loop\n" ++
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
  "sps_keys:\n  .zero 4096\n" ++       -- 128 x 32-byte slot keys
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
    Output: +0 count (expect 1); +8 key byte31 (expect 0x07); +16 value byte0 (expect 0). -/
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
  stagePredeployStoragePreloadData ++ "\n" ++          -- sps_* (null witness by default)
  ".balign 8\n" ++
  "spsp_out:\n  .zero 8256\n"

def ziskStagePredeployStoragePreloadProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskStagePredeployStoragePreloadPrologue
  dataAsm     := ziskStagePredeployStoragePreloadDataSection
}

end EvmAsm.Codegen
