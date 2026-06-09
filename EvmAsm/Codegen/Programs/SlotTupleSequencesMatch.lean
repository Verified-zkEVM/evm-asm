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

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-! ## slot_tuple_sequences_match
    a0 = BAL tuple-sequence ptr    a1 = BAL tuple count
    a2 = exec tuple-sequence ptr   a3 = exec tuple count
    a0 (output) = 0 sequences identical / 1 mismatch.
    Records are 40 bytes: block_access_index (u64) at +0, new_value (32B) at +8. -/
def slotTupleSequencesMatchFunction : String :=
  "slot_tuple_sequences_match:\n" ++
  "  bne a1, a3, .Lstsm_bad        # length mismatch -> reject\n" ++
  "  li t0, 0                      # i\n" ++
  ".Lstsm_loop:\n" ++
  "  beq t0, a1, .Lstsm_ok\n" ++
  "  slli t1, t0, 5; slli t2, t0, 3; add t1, t1, t2   # i*40\n" ++
  "  add t3, a0, t1                # BAL record i\n" ++
  "  add t4, a2, t1                # exec record i\n" ++
  "  ld t5, 0(t3);  ld t6, 0(t4);  bne t5, t6, .Lstsm_bad   # block_access_index\n" ++
  "  ld t5, 8(t3);  ld t6, 8(t4);  bne t5, t6, .Lstsm_bad   # value[0:8]\n" ++
  "  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lstsm_bad   # value[8:16]\n" ++
  "  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lstsm_bad   # value[16:24]\n" ++
  "  ld t5, 32(t3); ld t6, 32(t4); bne t5, t6, .Lstsm_bad   # value[24:32]\n" ++
  "  addi t0, t0, 1; j .Lstsm_loop\n" ++
  ".Lstsm_ok:\n" ++
  "  li a0, 0; ret\n" ++
  ".Lstsm_bad:\n" ++
  "  li a0, 1; ret"

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
