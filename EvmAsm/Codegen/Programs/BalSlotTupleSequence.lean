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
    +0  block_access_index (u64, little-endian as decoded by rlp_field_to_u64)
    +8  new_value (32-byte big-endian, left-padded)
  Returns a0 = tuple count for the matching slot (0 if the slot is absent or on any
  parse failure — conservative).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.RlpRead
import EvmAsm.Codegen.Programs.Tx

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## bal_slot_tuple_sequence
    a0 = AccountChanges RLP ptr   a1 = AccountChanges RLP length
    a2 = target slot key ptr (32-byte big-endian)   a3 = out buffer ptr
    a0 (output) = tuple count for the matching slot (0 if not found / parse failure). -/
def balSlotTupleSequenceFunction : String :=
  "bal_slot_tuple_sequence:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp)\n" ++
  "  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                    # AccountChanges ptr\n" ++
  "  mv s1, a1                    # AccountChanges len\n" ++
  "  mv s2, a2                    # target key ptr (32B BE)\n" ++
  "  mv s3, a3                    # out buffer ptr\n" ++
  "  # storage_changes = item 1\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 1; la a3, bts_scoff; la a4, bts_sclen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_scoff; ld t0, 0(t0); add s4, s0, t0   # storage_changes ptr\n" ++
  "  la t0, bts_sclen; ld s5, 0(t0)                   # storage_changes len\n" ++
  "  mv a0, s4; mv a1, s5; la a2, bts_cnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_cnt; ld s6, 0(t0)                     # slot count\n" ++
  "  li s7, 0                     # slot index\n" ++
  ".Lbts_sloop:\n" ++
  "  beq s7, s6, .Lbts_notfound   # scanned all slots, target absent -> 0\n" ++
  "  mv a0, s4; mv a1, s5; mv a2, s7; la a3, bts_eoff; la a4, bts_elen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_eoff; ld t0, 0(t0); add t1, s4, t0    # entry ptr\n" ++
  "  la t0, bts_elen; ld t2, 0(t0)                    # entry len\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 0; la a3, bts_koff; la a4, bts_klen\n" ++
  "  jal ra, rlp_list_nth_item                        # key = item 0\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_eoff; ld t0, 0(t0); add t1, s4, t0    # recompute entry ptr\n" ++
  "  la t0, bts_koff; ld t3, 0(t0); add t1, t1, t3    # key bytes ptr\n" ++
  "  la t0, bts_klen; ld t4, 0(t0)                    # key byte len\n" ++
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
  "  addi s7, s7, 1; j .Lbts_sloop\n" ++
  ".Lbts_match:\n" ++
  "  # value_list = item 1 of the matching entry (entry ptr = s4 + bts_eoff)\n" ++
  "  la t0, bts_eoff; ld t0, 0(t0); add t1, s4, t0\n" ++
  "  la t0, bts_elen; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, bts_voff; la a4, bts_vlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_eoff; ld t0, 0(t0); add t1, s4, t0\n" ++
  "  la t0, bts_voff; ld t3, 0(t0); add t1, t1, t3    # value_list ptr\n" ++
  "  la t0, bts_vlen; ld t2, 0(t0)                    # value_list len\n" ++
  "  mv s5, t1                    # reuse s5 = value_list ptr (sc len no longer needed)\n" ++
  "  mv s6, t2                    # reuse s6 = value_list len (slot count no longer needed)\n" ++
  "  mv a0, s5; mv a1, s6; la a2, bts_tcnt\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_tcnt; ld s7, 0(t0)                    # reuse s7 = tuple count\n" ++
  "  li s4, 0                     # reuse s4 = tuple index j (sc ptr no longer needed)\n" ++
  ".Lbts_tloop:\n" ++
  "  beq s4, s7, .Lbts_done\n" ++
  "  mv a0, s5; mv a1, s6; mv a2, s4; la a3, bts_toff; la a4, bts_tlen\n" ++
  "  jal ra, rlp_list_nth_item                        # tuple = nth(value_list, j)\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_toff; ld t0, 0(t0); add t1, s5, t0    # tuple ptr\n" ++
  "  la t0, bts_tlen; ld t2, 0(t0)                    # tuple len\n" ++
  "  # out record base = s3 + j*40  (40 = (j<<5) + (j<<3))\n" ++
  "  slli t3, s4, 5; slli t4, s4, 3; add t3, t3, t4; add a3, s3, t3   # out[j] base; bai -> +0\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 0\n" ++
  "  jal ra, rlp_field_to_u64                         # block_access_index -> out[j]+0\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  # new_value = item 1 of the tuple (tuple ptr = s5 + bts_toff)\n" ++
  "  la t0, bts_toff; ld t0, 0(t0); add t1, s5, t0\n" ++
  "  la t0, bts_tlen; ld t2, 0(t0)\n" ++
  "  mv a0, t1; mv a1, t2; li a2, 1; la a3, bts_noff; la a4, bts_nlen\n" ++
  "  jal ra, rlp_list_nth_item\n" ++
  "  bnez a0, .Lbts_notfound\n" ++
  "  la t0, bts_toff; ld t0, 0(t0); add t1, s5, t0\n" ++
  "  la t0, bts_noff; ld t3, 0(t0); add t1, t1, t3    # new_value bytes ptr\n" ++
  "  la t0, bts_nlen; ld t4, 0(t0)                    # new_value byte len\n" ++
  "  li t5, 32; bgtu t4, t5, .Lbts_notfound\n" ++
  "  # value dst = out[j] + 8 = s3 + j*40 + 8\n" ++
  "  slli t3, s4, 5; slli t6, s4, 3; add t3, t3, t6; add t6, s3, t3; addi t6, t6, 8   # value dst base\n" ++
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
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- Scratch for `bal_slot_tuple_sequence`. -/
def balSlotTupleSequenceData : String :=
  ".balign 8\n" ++
  "bts_scoff:\n  .zero 8\n" ++ "bts_sclen:\n  .zero 8\n" ++
  "bts_cnt:\n  .zero 8\n" ++
  "bts_eoff:\n  .zero 8\n" ++ "bts_elen:\n  .zero 8\n" ++
  "bts_koff:\n  .zero 8\n" ++ "bts_klen:\n  .zero 8\n" ++
  "bts_voff:\n  .zero 8\n" ++ "bts_vlen:\n  .zero 8\n" ++
  "bts_tcnt:\n  .zero 8\n" ++
  "bts_toff:\n  .zero 8\n" ++ "bts_tlen:\n  .zero 8\n" ++
  "bts_noff:\n  .zero 8\n" ++ "bts_nlen:\n  .zero 8\n" ++
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
  rlpListNthItemFunction ++ "\n" ++
  rlpListCountItemsFunction ++ "\n" ++
  rlpFieldToU64Function ++ "\n" ++
  ".Lbts_pdone:"

def ziskBalSlotTupleSequenceDataSection : String :=
  ".section .data\n" ++
  balSlotTupleSequenceData ++
  ziskRlpFieldToU64DataSection   -- rfu_offset/rfu_length scratch for rlp_field_to_u64

def ziskBalSlotTupleSequenceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBalSlotTupleSequencePrologue
  dataAsm     := ziskBalSlotTupleSequenceDataSection
}

end EvmAsm.Codegen
