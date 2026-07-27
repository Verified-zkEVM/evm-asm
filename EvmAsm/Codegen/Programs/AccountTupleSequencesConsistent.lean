/-
  EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent

  `account_tuple_sequences_consistent` (bead bmvmx.1.6.6 — the per-account all-slots
  tuple-sequence check) — the integration that closes the Q5 soundness gap: for one
  account, verify that EVERY storage slot's BAL-declared per-tx
  `(block_access_index, new_value)` tuple sequence equals the sequence execution
  actually produced (the spec hashes these into `header.block_access_list_hash`).

  Composes the three tuple-layer pieces per slot:
    - `bal_slot_tuple_sequence` (#8593) — the slot's declared tuples from the BAL;
    - `exec_log_slot_tuples`   (#8595) — the slot's net-change tuples reconstructed
      from the append-per-write storage exec-log + `exec_log_txindex`;
    - `slot_tuple_sequences_match` (#8596) — exact list-vs-list comparison.
  Iterates the account's `storage_changes` (AccountChanges item 1), extracts each
  `slot_key` (item 0 of the SlotChanges), and rejects on the first user-transaction
  slot whose sequences differ. Slots whose BAL tuple sequence starts at
  `block_access_index = 0` are system-transaction storage effects; the runtime exec log
  only records user transaction SSTOREs today, so those slots are skipped conservatively
  until system-tx tuple derivation is wired. A single-tx block degenerates to one tuple
  per slot (= the final), so this is a no-op there; it bites once the multi-tx loop sets
  `current_block_access_index` per tx (.57.11.6.3).

  Buffer note: `atsc_balbuf`/`atsc_execbuf` hold up to bsrMaxTuplesPerSlot tuples
  (40 B each) per slot (.66.1.2: gas-derived — per-slot tuple count is bounded by the
  block's transaction count, <= ~9.5k at 200M gas). bal_slot_tuple_sequence writes
  nothing and returns the true count above the cap; the call site bails to .Latsc_fail.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.BalValueReverseSAsm
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch
import EvmAsm.Codegen.Programs.SystemStorageSlotTuples
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## account_tuple_sequences_consistent
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = addrHash ptr (32B; this account's exec-log key)
    a3 = exec storage-log base    a4 = exec-log entry count    a5 = exec_log_txindex base
    a0 (output) = 0 every slot's tuple sequence matches exec / 1 mismatch (or parse fail). -/
def accountTupleSequencesConsistentFunction : String :=
  "account_tuple_sequences_consistent:\n" ++
  "  addi sp, sp, -96\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)\n" ++
  "  mv s0, a0                   # AccountChanges ptr\n" ++
  "  mv s1, a1                   # AccountChanges len\n" ++
  "  mv s2, a2                   # addrHash ptr\n" ++
  "  mv s3, a3                   # exec-log base\n" ++
  "  mv s4, a4                   # exec-log entry count\n" ++
  "  mv s5, a5                   # exec_log_txindex base\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Latsc_fail\n" ++
  "  mv s8, a1                                             # AccountChanges end\n" ++
  "  jal ra, rlp_walk_next                                # skip address item 0\n" ++
  "  bnez a1, .Latsc_fail\n" ++
  "  mv a1, s8\n" ++
  "  jal ra, rlp_walk_next                                # storage_changes = item 1\n" ++
  "  bnez a1, .Latsc_fail\n" ++
  "  sub s6, a0, a2; mv s7, a2                            # storage_changes ptr/len\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Latsc_fail\n" ++
  "  mv s8, a0                                             # storage_changes cursor\n" ++
  "  mv s9, a1                                             # storage_changes end\n" ++
  ".Latsc_loop:\n" ++
  "  beq s8, s9, .Latsc_ok\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Latsc_fail\n" ++
  "  mv s8, a0; sub t1, a0, a2; mv t2, a2                # SlotChanges entry ptr/len\n" ++
  "  mv a0, t1; mv a1, t2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Latsc_fail\n" ++
  "  jal ra, rlp_walk_next                                # slot_key = item 0\n" ++
  "  bnez a1, .Latsc_fail\n" ++
  "  sub t1, a0, a2                                       # key bytes ptr\n" ++
  "  mv t4, a2                                            # key byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Latsc_fail\n" ++
  "  # left-pad slot_key into atsc_key (32B)\n" ++
  "  la t6, atsc_key; mv t0, t6; li t5, 32\n" ++
  ".Latsc_kz:\n  beqz t5, .Latsc_kzd\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Latsc_kz\n" ++
  ".Latsc_kzd:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5\n" ++
  ".Latsc_kc:\n  beqz t4, .Latsc_kcd\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Latsc_kc\n" ++
  ".Latsc_kcd:\n" ++
  -- bmvmx.1.6.6: atsc_key is 32B BIG-endian (RLP) for the BAL search
  -- (bal_slot_tuple_sequence compares against the BE-left-padded BAL key,
  -- BalSlotTupleSequence.lean:36/80). The exec log is LITTLE-endian (slotKey @ +32 =
  -- EVM-stack 4 LE u64 limbs low-first, Storage.lean:19), so byte-reverse atsc_key ->
  -- atsc_key_le for exec_log_slot_tuples, AND reverse the BAL tuple VALUES BE->LE below
  -- (the exec side emits the LE log value verbatim). Mirrors bal_storage_matches_exec_log's
  -- bsme_krev/bsme_vrev. Old code passed BE atsc_key + BE values to BOTH -> the exec
  -- compare mismatched the LE log -> exec_count=0 vs bal_count>0 -> false-reject. Latent:
  -- only the interacting-mtx non-recipient-slot path (.57.11.6.3) reaches here.
  "  la t0, atsc_key; addi t0, t0, 31; la t1, atsc_key_le; li t2, 32\n" ++
  ".Latsc_klr:\n  beqz t2, .Latsc_klrd\n  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, -1; addi t1, t1, 1; addi t2, t2, -1; j .Latsc_klr\n" ++
  ".Latsc_klrd:\n" ++
  "  # BAL tuple sequence for this slot (searched by BE atsc_key)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, atsc_key; la a3, atsc_balbuf\n" ++
  "  jal ra, bal_slot_tuple_sequence\n" ++
  -- .66.1.2: > bsrMaxTuplesPerSlot -> the helper wrote nothing (returns the true count);
  -- bail conservatively instead of comparing against stale atsc_balbuf contents.
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu a0, t0, .Latsc_fail\n" ++
  "  la t0, atsc_balcount; sd a0, 0(t0)                   # bal_count\n" ++
  "  # reverse each BAL tuple's 32B value (BE -> LE) to match the LE exec output\n" ++
  "  mv t0, a0; la t1, atsc_balbuf                        # t0=count; record = bai@0, value@8\n" ++
  ".Latsc_vr:\n  beqz t0, .Latsc_vrd\n  addi t2, t1, 8\n" ++
  emitProgram BalValueReverseSAsm.balValueReverse_verified ++ "\n" ++
  "  addi t1, t1, 40; addi t0, t0, -1; j .Latsc_vr\n" ++
  ".Latsc_vrd:\n" ++
  "  # exec net-change tuple sequence for this slot: begin-system (idx0) then user (1..N) then end-system (idxN+1).\n" ++
  -- lv44p.2.2: point system_user_exec_log_slot_tuples at the REAL per-row system
  -- block_access_index array so end-of-block (EIP-7002/7251) rows order after the
  -- user txs (index N+1) instead of being mis-stamped 0 and placed first.
  "  la t0, sust_sys_txindex_ptr; la t1, bv_system_storage_txindex; sd t1, 0(t0)\n" ++
  -- bmvmx.5.5.10 PR-2: on the mtx lane the per-tx USER side arena (bv_user_storage_log,
  -- captured after every user dispatch) is the complete user-write source; the
  -- caller-passed live log holds only the LAST dispatch's rows. Prefer the arena when
  -- populated; single-tx lanes leave it empty and keep the legacy live-log source.
  "  la t0, bv_user_storage_log_count; ld t1, 0(t0)\n" ++
  "  beqz t1, .Latsc_user_live\n" ++
  "  la a4, bv_user_storage_log; mv a5, t1; la a6, bv_user_storage_txindex; j .Latsc_user_set\n" ++
  ".Latsc_user_live:\n" ++
  "  mv a4, s3; mv a5, s4; mv a6, s5\n" ++
  ".Latsc_user_set:\n" ++
  "  mv a0, s2; la a1, atsc_key_le; la a2, bv_system_storage_log; la t0, bv_system_storage_log_count; ld a3, 0(t0); la a7, atsc_execbuf\n" ++
  "  jal ra, system_user_exec_log_slot_tuples\n" ++
  "  mv t6, a0                                            # exec_count\n" ++
  -- fhsxz.2.4.2.66.1.1: symmetric to the BAL-side cap bail above. exec_log_slot_tuples
  -- stops writing at bsrMaxTuplesPerSlot records (atsc_execbuf capacity) but returns the
  -- true count; > cap means the tail records were not written, so bail conservatively
  -- instead of comparing against stale/partial atsc_execbuf contents.
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu t6, t0, .Latsc_fail\n" ++
  "  # exact list-vs-list comparison\n" ++
  "  la a0, atsc_balbuf; la t0, atsc_balcount; ld a1, 0(t0); la a2, atsc_execbuf; mv a3, t6\n" ++
  "  jal ra, slot_tuple_sequences_match\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  ".Latsc_next_slot:\n" ++
  "  j .Latsc_loop\n" ++
  ".Latsc_ok:\n" ++
  "  li a0, 0; j .Latsc_ret\n" ++
  ".Latsc_fail:\n" ++
  "  li a0, 1\n" ++
  ".Latsc_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)\n" ++
  "  addi sp, sp, 96\n" ++
  "  ret"

/-- Scratch + tuple buffers for `account_tuple_sequences_consistent`. -/
def accountTupleSequencesConsistentData : String :=
  ".balign 8\n" ++
  "atsc_balcount:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "atsc_key:\n  .zero 32\n" ++
  "atsc_key_le:\n  .zero 32\n" ++       -- LE byte-reverse of atsc_key for the exec-log search (bmvmx.1.6.6)
  "atsc_balbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++   -- .66.1.2: bsrMaxTuplesPerSlot tuples * 40B (was 256; one net-change tuple per tx, ~9.5k max at 200M)
  "atsc_execbuf:\n  .zero " ++ toString (bsrMaxTuplesPerSlot * 40) ++ "\n" ++
  systemUserExecLogSlotTuplesData

def accountTupleSequencesConsistentEmptySystemData : String :=
  ".balign 8\n" ++
  "bv_system_storage_log_count:\n  .zero 8\n" ++
  -- lv44p.2.2: the consistency fn now points sust_sys_txindex_ptr at this array.
  -- The standalone probe runs an empty system log (count 0), so it is never read,
  -- but the symbol must resolve at link time.
  "bv_system_storage_txindex:\n  .zero 16\n" ++
  ".balign 32\n" ++
  "bv_system_storage_log:\n  .zero " ++ toString bvStorageLogRowBytes ++ "\n" ++
  -- bmvmx.5.5.10 PR-2: link stubs so the per-account fn's user-arena preference
  -- resolves; count 0 keeps the probe on the legacy live-log path.  Sized from
  -- `bvStorageLogRowBytes` (one row) so a stride change cannot leave this probe
  -- reserving less than one row while the scan still strides by 128.
  ".balign 8\n" ++
  "bv_user_storage_log_count:\n  .zero 8\n" ++
  "bv_user_storage_txindex:\n  .zero " ++
    toString (2 * bvStorageLogTxindexEntryBytes) ++ "\n" ++
  ".balign 32\n" ++
  "bv_user_storage_log:\n  .zero " ++ toString bvStorageLogRowBytes ++ "\n"

/-- `zisk_account_tuple_sequences_consistent`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : AccountChanges byte length
      bytes 16..48 : addrHash (32B; this account's exec-log key)
      bytes 48..56 : exec-log entry count
      bytes 56..    : exec_log_txindex (count × 8B), exec-log (count × 128B), AccountChanges RLP
    Output: bytes 0..8 = status (0 consistent / 1 mismatch). -/
def ziskAccountTupleSequencesConsistentPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000\n" ++
  "  ld a1, 8(t6)                # AccountChanges len\n" ++
  "  addi a2, t6, 16             # addrHash ptr\n" ++
  "  ld a4, 48(t6)               # exec-log entry count\n" ++
  "  addi a5, t6, 56             # txindex array base\n" ++
  "  slli t0, a4, 3; add a3, a5, t0   # exec-log base = txindex_base + count*8\n" ++
  "  slli t0, a4, 7; add a0, a3, t0   # AccountChanges ptr = log_base + count*128\n" ++
  "  jal ra, account_tuple_sequences_consistent\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Latsc_pdone\n" ++
  accountTupleSequencesConsistentFunction ++ "\n" ++
  balSlotTupleSequenceFunction ++ "\n" ++
  systemUserExecLogSlotTuplesFunction ++ "\n" ++
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Latsc_pdone:"

def ziskAccountTupleSequencesConsistentDataSection : String :=
  ".section .data\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++
  accountTupleSequencesConsistentEmptySystemData ++ "\n" ++
  balSlotTupleSequenceData ++ "\n" ++          -- bts_* scratch
  ziskRlpFieldToU64DataSection ++ "\n" ++      -- rfu_* scratch (rlp_field_to_u64)
  execLogSlotTuplesData                        -- els_* scratch

def ziskAccountTupleSequencesConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountTupleSequencesConsistentPrologue
  dataAsm     := ziskAccountTupleSequencesConsistentDataSection
}

end EvmAsm.Codegen
