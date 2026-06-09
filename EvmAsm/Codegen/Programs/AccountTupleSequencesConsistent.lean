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
  `slot_key` (item 0 of the SlotChanges), and rejects on the first slot whose sequences
  differ. A single-tx block degenerates to one tuple per slot (= the final), so this is
  a no-op there; it bites once the multi-tx loop sets `current_block_access_index` per
  tx (.57.11.6.3).

  Buffer note: `atsc_balbuf`/`atsc_execbuf` hold up to 256 tuples (40 B each) per slot;
  the producers write `count` records, so wiring against blocks whose per-slot tuple
  count can exceed 256 must enlarge these (bounded by the block's transaction count).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch

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
  "  mv a0, s0; mv a1, s1; li a2, 1; la a3, atsc_scoff; la a4, atsc_sclen\n" ++
  "  jal ra, rlp_list_nth_item                            # storage_changes = item 1\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  "  la t0, atsc_scoff; ld t1, 0(t0); add s6, s0, t1      # storage_changes ptr\n" ++
  "  la t0, atsc_sclen; ld s7, 0(t0)                      # storage_changes len\n" ++
  "  mv a0, s6; mv a1, s7; la a2, atsc_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  "  la t0, atsc_cnt; ld s8, 0(t0)                        # slot count\n" ++
  "  li s9, 0                    # slot index\n" ++
  ".Latsc_loop:\n" ++
  "  beq s9, s8, .Latsc_ok\n" ++
  "  mv a0, s6; mv a1, s7; mv a2, s9; la a3, atsc_eoff; la a4, atsc_elen\n" ++
  "  jal ra, rlp_list_nth_item                            # SlotChanges entry = nth(sc, i)\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  "  la t0, atsc_eoff; ld t1, 0(t0); add t1, s6, t1       # entry ptr\n" ++
  "  la t0, atsc_elen; ld t2, 0(t0)                       # entry len\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 0; la a3, atsc_koff; la a4, atsc_klen\n" ++
  "  jal ra, rlp_list_nth_item                            # slot_key = item 0\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  "  la t0, atsc_eoff; ld t1, 0(t0); add t1, s6, t1       # recompute entry ptr\n" ++
  "  la t0, atsc_koff; ld t3, 0(t0); add t1, t1, t3       # key bytes ptr\n" ++
  "  la t0, atsc_klen; ld t4, 0(t0)                       # key byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Latsc_fail\n" ++
  "  # left-pad slot_key into atsc_key (32B)\n" ++
  "  la t6, atsc_key; mv t0, t6; li t5, 32\n" ++
  ".Latsc_kz:\n  beqz t5, .Latsc_kzd\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Latsc_kz\n" ++
  ".Latsc_kzd:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5\n" ++
  ".Latsc_kc:\n  beqz t4, .Latsc_kcd\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Latsc_kc\n" ++
  ".Latsc_kcd:\n" ++
  "  # BAL tuple sequence for this slot\n" ++
  "  mv a0, s0; mv a1, s1; la a2, atsc_key; la a3, atsc_balbuf\n" ++
  "  jal ra, bal_slot_tuple_sequence\n" ++
  "  la t0, atsc_balcount; sd a0, 0(t0)                   # bal_count\n" ++
  "  # exec net-change tuple sequence for this slot\n" ++
  "  mv a0, s2; la a1, atsc_key; mv a2, s3; mv a3, s4; mv a4, s5; la a5, atsc_execbuf\n" ++
  "  jal ra, exec_log_slot_tuples\n" ++
  "  mv t6, a0                                            # exec_count\n" ++
  "  # exact list-vs-list comparison\n" ++
  "  la a0, atsc_balbuf; la t0, atsc_balcount; ld a1, 0(t0); la a2, atsc_execbuf; mv a3, t6\n" ++
  "  jal ra, slot_tuple_sequences_match\n" ++
  "  bnez a0, .Latsc_fail\n" ++
  "  addi s9, s9, 1; j .Latsc_loop\n" ++
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
  "atsc_scoff:\n  .zero 8\n" ++ "atsc_sclen:\n  .zero 8\n" ++
  "atsc_cnt:\n  .zero 8\n" ++
  "atsc_eoff:\n  .zero 8\n" ++ "atsc_elen:\n  .zero 8\n" ++
  "atsc_koff:\n  .zero 8\n" ++ "atsc_klen:\n  .zero 8\n" ++
  "atsc_balcount:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "atsc_key:\n  .zero 32\n" ++
  "atsc_balbuf:\n  .zero 10240\n" ++   -- up to 256 tuples * 40B
  "atsc_execbuf:\n  .zero 10240\n"

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
  execLogSlotTuplesFunction ++ "\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Latsc_pdone:"

def ziskAccountTupleSequencesConsistentDataSection : String :=
  ".section .data\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++
  balSlotTupleSequenceData ++ "\n" ++          -- bts_* scratch
  ziskRlpFieldToU64DataSection ++ "\n" ++      -- rfu_* scratch (rlp_field_to_u64)
  execLogSlotTuplesData                        -- els_* scratch

def ziskAccountTupleSequencesConsistentProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskAccountTupleSequencesConsistentPrologue
  dataAsm     := ziskAccountTupleSequencesConsistentDataSection
}

end EvmAsm.Codegen
