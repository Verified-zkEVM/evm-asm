/-
  EvmAsm.Codegen.Programs.BalSlotTupleSequence

  `bal_slot_tuple_sequence` (bead bmvmx.1.6.8 — foundation for the bmvmx.1.6.6 tuple
  comparator) — extract a single slot's FULL per-tx `(block_access_index, new_value)`
  tuple SEQUENCE from a BAL AccountChanges' `storage_changes`.

  This is the BAL-side companion of the per-tx tuple-sequence soundness layer
  (bmvmx.1.6.6): where `bal_storage_change_values` (#bmvmx.1.6.1) keeps only the LAST
  tuple's value per slot (the block-final), this keeps EVERY tuple — the sequence the
  spec hashes into `header.block_access_list_hash`. The eventual comparator
  reconstructs the same sequence from execution (the append-per-write storage exec-log
  grouped by `exec_log_txindex`, last-write-per-tx) and compares the two list-vs-list.

  AccountChanges = RLP `[address, storage_changes, ...]`; each `storage_changes` entry
  is `[slot_key (Bytes32), [ [block_access_index, new_value (Bytes32)] ... ] ]`.

  Output buffer: `count` × 40-byte records, one per tuple in order:
    +0  block_access_index (u64, little-endian as decoded by rlp_content_to_u64)
    +8  new_value (32-byte big-endian, left-padded)
  Returns a0 = tuple count for the matching slot (0 if the slot is absent or on any
  parse failure — conservative).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpWalk
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_slot_tuple_sequence
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = target slot key ptr (32-byte big-endian)   a3 = out buffer ptr
         (caller buffer must hold bsrMaxTuplesPerSlot x 40-byte records)
    a0 (output) = tuple count for the matching slot (0 if not found / parse failure;
    if > bsrMaxTuplesPerSlot, NOTHING is written and the true count is returned —
    the caller must treat counts above the cap as a conservative bail). -/
def balSlotTupleSequenceFunction : String :=
  "bal_slot_tuple_sequence:\n" ++
  "  addi sp, sp, -112\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)\n" ++
  "  mv s0, a0                    # AccountChanges ptr\n" ++
  "  mv s1, a1                    # AccountChanges len\n" ++
  "  mv s2, a2                    # target key ptr (32B BE)\n" ++
  "  mv s3, a3                    # out buffer ptr\n" ++
  "  # storage_changes = item 1\n" ++
  "  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s6, a1                    # AccountChanges end\n" ++
  "  jal ra, rlp_walk_next        # skip address item 0\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv a1, s6; jal ra, rlp_walk_next                  # storage_changes = item 1\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  sub s4, a0, a2; mv s5, a2    # storage_changes ptr/len\n" ++
  "  mv a0, s4; mv a1, s5; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s6, a0                    # storage_changes cursor\n" ++
  "  mv s7, a1                    # storage_changes end\n" ++
  ".Lbts_sloop:\n" ++
  "  beq s6, s7, .Lbts_notfound   # scanned all slots, target absent -> 0\n" ++
  "  mv a0, s6; mv a1, s7; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv s6, a0; sub s8, a0, a2; mv s9, a2             # SlotChanges entry ptr/len\n" ++
  "  mv a0, s8; mv a1, s9; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s11, a1                   # SlotChanges end\n" ++
  "  jal ra, rlp_walk_next                        # key = item 0\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv s10, a0                   # cursor after key, for value_list on match\n" ++
  "  sub t1, a0, a2               # key bytes ptr\n" ++
  "  mv t4, a2                    # key byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbts_notfound\n" ++
  "  # build 32B left-padded key in bts_keypad\n" ++
  "  la t6, bts_keypad; mv t0, t6; li t5, 32\n" ++
  ".Lbts_kz:\n  beqz t5, .Lbts_kzd\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbts_kz\n" ++
  ".Lbts_kzd:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5        # dst = pad + (32 - klen)\n" ++
  ".Lbts_kc:\n  beqz t4, .Lbts_kcd\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbts_kc\n" ++
  ".Lbts_kcd:\n" ++
  "  # compare bts_keypad vs target key (s2), 32 bytes\n" ++
  "  la t6, bts_keypad; mv t0, zero\n" ++
  ".Lbts_mc:\n" ++
  "  li t1, 32; beq t0, t1, .Lbts_match\n" ++
  "  add t1, t6, t0; lbu t2, 0(t1); add t1, s2, t0; lbu t3, 0(t1)\n" ++
  "  bne t2, t3, .Lbts_snext\n" ++
  "  addi t0, t0, 1; j .Lbts_mc\n" ++
  ".Lbts_snext:\n" ++
  "  j .Lbts_sloop\n" ++
  ".Lbts_match:\n" ++
  "  # value_list = item 1 of the matching entry\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  sub s5, a0, a2; mv s6, a2    # value_list ptr/len\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s10, a0; mv s11, a1; li s7, 0                 # count tuples first\n" ++
  ".Lbts_count_loop:\n" ++
  "  beq s10, s11, .Lbts_count_done\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv s10, a0; addi s7, s7, 1; j .Lbts_count_loop\n" ++
  ".Lbts_count_done:\n" ++
  -- fhsxz.2.4.2.66.1.1/.66.1.2: bound the output. Every consumer buffer (sps_tuples,
  -- atsc_balbuf) holds bsrMaxTuplesPerSlot 40-byte records; an adversarial BAL can
  -- declare more tuples than any legitimate <=200M block (one net-change tuple per tx).
  -- Above the cap, write NOTHING and return the true count (jump straight to done) so
  -- callers bail conservatively instead of this loop overflowing adjacent .data.
  "  li t0, " ++ toString bsrMaxTuplesPerSlot ++ "; bgtu s7, t0, .Lbts_done\n" ++
  "  mv a0, s5; mv a1, s6; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s10, a0; mv s11, a1; li s4, 0                 # tuple cursor/end/index\n" ++
  ".Lbts_tloop:\n" ++
  "  beq s4, s7, .Lbts_done\n" ++
  "  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv s10, a0; sub t1, a0, a2; mv t2, a2            # tuple ptr/len\n" ++
  "  # out record base = s3 + j*40  (40 = (j<<5) + (j<<3))\n" ++
  "  slli t3, s4, 5; slli t4, s4, 3; add t3, t3, t4; add s8, s3, t3   # out[j] base\n" ++
  "  mv a0, t1; mv a1, t2; jal ra, rlp_walk_init\n" ++
  "  bnez a2, .Lbts_notfound\n" ++
  "  mv s9, a1                    # tuple end\n" ++
  "  jal ra, rlp_walk_next                         # block_access_index\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  mv t0, a0; sub a0, a0, a2; mv a1, a2; mv s6, t0; jal ra, rlp_content_to_u64\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  sd a0, 0(s8)                                  # block_access_index -> out[j]+0\n" ++
  "  # new_value = item 1 of the tuple\n" ++
  "  mv a0, s6; mv a1, s9; jal ra, rlp_walk_next\n" ++
  "  bnez a1, .Lbts_notfound\n" ++
  "  sub t1, a0, a2                                 # new_value bytes ptr\n" ++
  "  mv t4, a2                                      # new_value byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbts_notfound\n" ++
  "  # value dst = out[j] + 8 = s3 + j*40 + 8\n" ++
  "  addi t6, s8, 8                  # value dst base\n" ++
  "  mv t0, t6; li t5, 32\n" ++
  ".Lbts_vz:\n  beqz t5, .Lbts_vzd\n  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbts_vz\n" ++
  ".Lbts_vzd:\n" ++
  "  li t5, 32; sub t5, t5, t4; add t0, t6, t5\n" ++
  ".Lbts_vc:\n  beqz t4, .Lbts_vcd\n  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbts_vc\n" ++
  ".Lbts_vcd:\n" ++
  "  addi s4, s4, 1; j .Lbts_tloop\n" ++
  ".Lbts_done:\n" ++
  "  mv a0, s7                    # tuple count\n" ++
  "  j .Lbts_ret\n" ++
  ".Lbts_notfound:\n" ++
  "  li a0, 0\n" ++
  ".Lbts_ret:\n" ++
  "  ld ra, 0(sp)\n" ++
  "  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)\n" ++
  "  addi sp, sp, 112\n" ++
  "  ret"

/-- Scratch for `bal_slot_tuple_sequence`. -/
def balSlotTupleSequenceData : String :=
  ".balign 8\n" ++
  ".balign 32\n" ++
  "bts_keypad:\n  .zero 32\n"

/-- `zisk_bal_slot_tuple_sequence`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : AccountChanges byte length
      bytes 16..48 : target slot key (32B big-endian)
      bytes 48..    : the AccountChanges RLP
    Output: bytes 0..8 = tuple count; then count × 40-byte records at 0xa0010008. -/
def ziskBalSlotTupleSequencePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # AccountChanges len\n" ++
  "  addi a2, a5, 16             # target slot key ptr (32B)\n" ++
  "  addi a0, a5, 48             # AccountChanges ptr\n" ++
  "  li a3, 0xa0010008           # out buffer = OUTPUT + 8\n" ++
  "  jal ra, bal_slot_tuple_sequence\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # tuple count\n" ++
  "  j .Lbts_pdone\n" ++
  balSlotTupleSequenceFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  ".Lbts_pdone:"

def ziskBalSlotTupleSequenceDataSection : String :=
  ".section .data\n" ++
  balSlotTupleSequenceData

def ziskBalSlotTupleSequenceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSlotTupleSequencePrologue
  dataAsm     := ziskBalSlotTupleSequenceDataSection
}

end EvmAsm.Codegen
