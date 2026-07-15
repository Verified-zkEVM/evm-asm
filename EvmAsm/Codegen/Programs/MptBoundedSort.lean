/-
  EvmAsm.Codegen.Programs.MptBoundedSort

  sd13v's first executable component: an in-place MSD radix sort for the
  normalized final state-change descriptors.  It deliberately has no route
  from the verdict yet; the root builder is attached only after its
  committed-final-value proof obligation is closed.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

/-! ## `mpt_bounded_sort_changes`

The input is an array of 40-byte state-change descriptors (`path` at offset
zero).  All accepted state keys have exactly 64 nibbles.  The routine performs
an in-place MSD partition at each depth and pushes only non-singleton ranges.
The pending stack contains `(start, end, depth, _)` records.  At most 16 ranges
are introduced at a depth, so the 64 * 16 depth/fanout capacity is sufficient;
the routine checks both the change and stack bounds before every write.

ABI: `a0 = descriptors`, `a1 = count`; returns `a0 = 0` on success, `1` on a
malformed nibble or capacity violation. -/
def mptBoundedSortChangesFunction : String :=
  "  .globl mpt_bounded_sort_changes\n" ++
  "mpt_bounded_sort_changes:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  li t0, " ++ toString bsrMaxStateChanges ++ "; bgtu a1, t0, .Lmbs_fail\n" ++
  "  mv s0, a0; mv s1, a1; la s2, bsr_sort_ranges; li s3, 0\n" ++
  "  beqz s1, .Lmbs_ok\n" ++
  "  sd zero, 0(s2); sd s1, 8(s2); sd zero, 16(s2); sd zero, 24(s2); li s3, 1\n" ++
  ".Lmbs_pop:\n" ++
  "  beqz s3, .Lmbs_ok\n" ++
  "  addi s3, s3, -1; slli t0, s3, 5; add t0, s2, t0\n" ++
  "  ld s4, 0(t0); ld s5, 8(t0); ld s6, 16(t0)\n" ++
  "  addi t1, s4, 1; bgeu t1, s5, .Lmbs_pop\n" ++
  "  li t1, " ++ toString bsrMptKeyNibbles ++ "; bgeu s6, t1, .Lmbs_pop\n" ++
  "  mv s7, s4; li t6, 0\n" ++
  ".Lmbs_digit:\n" ++
  "  li t0, " ++ toString bsrMptRadixFanout ++ "; beq t6, t0, .Lmbs_pop\n" ++
  "  mv t1, s7\n" ++
  ".Lmbs_scan:\n" ++
  "  beq t1, s5, .Lmbs_group\n" ++
  "  slli t0, t1, 5; slli t2, t1, 3; add t0, t0, t2; add t0, s0, t0; ld t2, 0(t0); add t2, t2, s6; lbu t3, 0(t2)\n" ++
  "  li t4, " ++ toString bsrMptRadixFanout ++ "; bgeu t3, t4, .Lmbs_fail\n" ++
  "  bne t3, t6, .Lmbs_scan_next\n" ++
  "  beq t1, s7, .Lmbs_scan_match\n" ++
  "  slli t2, s7, 5; slli t3, s7, 3; add t2, t2, t3; add t2, s0, t2\n" ++
  "  la t3, bsr_builder_frames; li t4, 5\n" ++
  ".Lmbs_swap:\n" ++
  "  ld t5, 0(t0); sd t5, 0(t3); ld t5, 0(t2); sd t5, 0(t0); ld t5, 0(t3); sd t5, 0(t2); addi t0, t0, 8; addi t2, t2, 8; addi t3, t3, 8; addi t4, t4, -1; bnez t4, .Lmbs_swap\n" ++
  ".Lmbs_scan_match:\n" ++
  "  addi s7, s7, 1\n" ++
  ".Lmbs_scan_next:\n" ++
  "  addi t1, t1, 1; j .Lmbs_scan\n" ++
  ".Lmbs_group:\n" ++
  "  addi t0, s4, 1; bgeu t0, s7, .Lmbs_digit_next\n" ++
  "  li t0, " ++ toString bsrMptSortRangeStackCapacity ++ "; bgeu s3, t0, .Lmbs_fail\n" ++
  "  slli t0, s3, 5; add t0, s2, t0; sd s4, 0(t0); sd s7, 8(t0); addi t1, s6, 1; sd t1, 16(t0); sd zero, 24(t0); addi s3, s3, 1\n" ++
  ".Lmbs_digit_next:\n" ++
  "  mv s4, s7; addi t6, t6, 1; j .Lmbs_digit\n" ++
  ".Lmbs_fail:\n" ++
  "  li a0, 1; j .Lmbs_ret\n" ++
  ".Lmbs_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lmbs_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 80; ret\n"

end EvmAsm.Codegen
