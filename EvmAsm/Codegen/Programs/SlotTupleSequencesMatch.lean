/-
  EvmAsm.Codegen.Programs.SlotTupleSequencesMatch

  `slot_tuple_sequences_match` (bead bmvmx.1.6.6 — the per-slot tuple-sequence check) —
  the consensus-binding comparator that closes the per-tx tuple-sequence soundness gap
  (the original Q5 finding): a malicious producer can commit a BAL with correct per-slot
  FINAL values but WRONG/EXTRA/MISSING intermediate `(block_access_index, new_value)`
  tuples; the spec rejects (the committed BAL != build(exec), so the hashes differ) but a
  finals-only guest would accept. This compares the two per-slot tuple SEQUENCES exactly.

  It is a pure list-vs-list equality on the two sequences:
    - BAL side  : `bal_slot_tuple_sequence` (#8593) — the slot's declared tuples;
    - exec side : `exec_log_slot_tuples`   (#8595) — the slot's reconstructed net-changes.
  Each sequence is `count` × 40-byte records `[block_access_index u64 @+0 | value 32B @+8]`,
  in increasing block_access_index order on both sides, so an honest BAL yields identical
  arrays. Any difference in length, index, or value is a reject.

  Keeping this comparator independent of the two producers (it takes the prepared arrays)
  means it composes cleanly in the all-slots wrapper once both foundations land.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## slot_tuple_sequences_match
    a0 = BAL tuple-sequence ptr    a1 = BAL tuple count
    a2 = exec tuple-sequence ptr   a3 = exec tuple count
    a0 (output) = 0 sequences identical / 1 mismatch.
    Records are 40 bytes: block_access_index (u64) at +0, new_value (32B) at +8. -/
def slotTupleSequencesMatch_prog : Program :=
  [ .BNE .x11 .x13 (108 : BitVec 13),
    .LI .x5 (0 : Word),
    .BEQ .x5 .x11 (92 : BitVec 13),
    .SLLI .x6 .x5 (5 : BitVec 6),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .ADD .x6 .x6 .x7,
    .ADD .x28 .x10 .x6,
    .ADD .x29 .x12 .x6,
    .LD .x30 .x28 (0 : BitVec 12),
    .LD .x31 .x29 (0 : BitVec 12),
    .BNE .x30 .x31 (68 : BitVec 13),
    .LD .x30 .x28 (8 : BitVec 12),
    .LD .x31 .x29 (8 : BitVec 12),
    .BNE .x30 .x31 (56 : BitVec 13),
    .LD .x30 .x28 (16 : BitVec 12),
    .LD .x31 .x29 (16 : BitVec 12),
    .BNE .x30 .x31 (44 : BitVec 13),
    .LD .x30 .x28 (24 : BitVec 12),
    .LD .x31 .x29 (24 : BitVec 12),
    .BNE .x30 .x31 (32 : BitVec 13),
    .LD .x30 .x28 (32 : BitVec 12),
    .LD .x31 .x29 (32 : BitVec 12),
    .BNE .x30 .x31 (20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .JAL .x0 (-88 : BitVec 21),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def slotTupleSequencesMatchFunction : String :=
  "slot_tuple_sequences_match:\n" ++ emitProgram slotTupleSequencesMatch_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `slotTupleSequencesMatch_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem slotTupleSequencesMatchFunction_eq_prog :
    slotTupleSequencesMatchFunction = "slot_tuple_sequences_match:\n" ++ emitProgram slotTupleSequencesMatch_prog := rfl

#guard slotTupleSequencesMatchFunction.startsWith "slot_tuple_sequences_match:\n"
#guard slotTupleSequencesMatch_prog.length = 29
/-- `zisk_slot_tuple_sequences_match`: focused probe.
    Input (after the ziskemu length wrapper at 0x40000000):
      bytes  8..16 : BAL tuple count
      bytes 16..24 : exec tuple count
      bytes 24..    : BAL sequence (count × 40B), then exec sequence (count × 40B)
    Output: bytes 0..8 = status (0 match / 1 mismatch). -/
def ziskSlotTupleSequencesMatchPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # BAL tuple count\n" ++
  "  ld a3, 16(a5)               # exec tuple count\n" ++
  "  addi a0, a5, 24             # BAL sequence ptr (0x40000018, 8-aligned)\n" ++
  "  slli t0, a1, 5; slli t1, a1, 3; add t0, t0, t1   # BAL count * 40\n" ++
  "  add a2, a0, t0              # exec sequence ptr = BAL ptr + BAL_count*40\n" ++
  "  jal ra, slot_tuple_sequences_match\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # status\n" ++
  "  j .Lstsm_pdone\n" ++
  slotTupleSequencesMatchFunction ++ "\n" ++
  ".Lstsm_pdone:"

def ziskSlotTupleSequencesMatchProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSlotTupleSequencesMatchPrologue
  dataAsm     := ""
}

end EvmAsm.Codegen
