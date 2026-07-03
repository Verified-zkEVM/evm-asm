/-
  EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopFromShapeMod

  Full n=3 v5 stack-pre → unified-post path with the carry hypothesis DISCHARGED
  FROM SHAPE.  Wraps `evm_mod_n3_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry`
  (#7540): instead of taking `loopN3SelectedBorrowCarryV5` as a hypothesis, it
  discharges it via `loopN3SelectedBorrowCarryV5_of_shape` (#7527), and accepts the
  borrow flags in the CLEAN `ult (fullDivN3R1V5 bltu_1 …).2.2.2.1 v2'` form (rather
  than #7540's `iterN3Max`/`iterWithDoubleAddback` `match` form), bridged via the
  dispatch-form equalities `fullDivN3R1V5_true`/`fullDivN3R1V5_false`.  This removes
  the last shape-derived obligation from the n=3 loop path — the direct input to the
  n=3 lane.  n3 mirror of `evm_div_n2_stack_pre_to_unified_post_v5_noNop_fromShape`.
  Bead `evm-asm-wbc4i.9.3.3.3.4`.
-/

import EvmAsm.Evm64.DivMod.Compose.FullPathN3V5NoNopPreloopBorrowCarryMod
import EvmAsm.Evm64.DivMod.Spec.N3V5BundleOfShape

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Full n=3 v5 stack-pre → unified-post, with the borrow-carry bundle discharged
    from shape; borrow flags in the clean `fullDivN3R1V5` form. -/
theorem evm_mod_n3_stack_pre_to_unified_post_v5_noNop_fromShape
    (bltu_1 bltu_0 : Bool) (sp base : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem : Word)
    (jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2nz : b2 ≠ 0)
    (hshift_nz : (clzResult b2).1 ≠ 0)
    (halign : ((base + div128CallRetOff) + signExtend12 (0 : BitVec 12)) &&& ~~~(1 : Word) =
      base + div128CallRetOff)
    (hbltu_1 : bltu_1 =
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hbltu_0 : bltu_0 =
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    cpsTripleWithin (8 + 21 + 24 + 4 + 21 + 21 + 4 + 468) base (base + denormOff)
      (modCode_noNop_v5 base)
      (((.x12 ↦ᵣ sp) ** (.x5 ↦ᵣ v5) ** (.x10 ↦ᵣ v10) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x6 ↦ᵣ v6) ** (.x7 ↦ᵣ v7) ** (.x2 ↦ᵣ x2In) **
        (.x9 ↦ᵣ x9In) **
        ((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + 32) ↦ₘ b0) ** ((sp + 40) ↦ₘ b1) **
        ((sp + 48) ↦ₘ b2) ** ((sp + 56) ↦ₘ b3) **
        ((sp + signExtend12 4088) ↦ₘ q0) ** ((sp + signExtend12 4080) ↦ₘ q1) **
        ((sp + signExtend12 4072) ↦ₘ q2) ** ((sp + signExtend12 4064) ↦ₘ q3) **
        ((sp + signExtend12 4056) ↦ₘ u0Old) ** ((sp + signExtend12 4048) ↦ₘ u1Old) **
        ((sp + signExtend12 4040) ↦ₘ u2Old) ** ((sp + signExtend12 4032) ↦ₘ u3Old) **
        ((sp + signExtend12 4024) ↦ₘ u4Old) **
        ((sp + signExtend12 4016) ↦ₘ u5) ** ((sp + signExtend12 4008) ↦ₘ u6) **
        ((sp + signExtend12 4000) ↦ₘ u7) ** ((sp + signExtend12 3984) ↦ₘ nMem) **
        ((sp + signExtend12 3992) ↦ₘ shiftMem)) **
       ((.x11 ↦ᵣ v11Old) ** ((sp + signExtend12 3976) ↦ₘ jMem) **
        (sp + signExtend12 3968 ↦ₘ retMem) **
        (sp + signExtend12 3960 ↦ₘ dMem) **
        (sp + signExtend12 3952 ↦ₘ dloMem) **
        (sp + signExtend12 3944 ↦ₘ scratchUn0) **
        (sp + signExtend12 3936 ↦ₘ scratchMem) **
        (.x1 ↦ᵣ raVal)))
      ((loopN3UnifiedPostV5NoX1 bltu_1 bltu_0 sp base
        (fullDivN3NormV b0 b1 b2 b3).1
        (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.2
        (fullDivN3NormU a0 a1 a2 a3 b2).2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
        (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
        (0 : Word)
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        retMem dMem dloMem scratchUn0 scratchMem **
        (.x1 ↦ᵣ raVal)) **
       (((sp + 0) ↦ₘ a0) ** ((sp + 8) ↦ₘ a1) **
        ((sp + 16) ↦ₘ a2) ** ((sp + 24) ↦ₘ a3) **
        ((sp + signExtend12 4072) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4064) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4008) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 4000) ↦ₘ (0 : Word)) **
        ((sp + signExtend12 3992) ↦ₘ (clzResult b2).1))) := by
  apply evm_mod_n3_preloop_loop_unified_exact_x1_scratch_v5_noNop_borrowCarry
    bltu_1 bltu_0 sp base a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
    jMem retMem dMem dloMem scratchUn0 scratchMem raVal x9In x2In
    hbnz hb3z hb2nz hshift_nz halign hbltu_1
  case hbltu_0 =>
    cases bltu_1 <;> simpa [fullDivN3R1V5_true, fullDivN3R1V5_false] using hbltu_0
  case hcarry =>
    apply loopN3SelectedBorrowCarryV5_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      bltu_1 bltu_0 hb3z hb2nz hshift_nz
    · intro h; rw [← hbltu_1]; exact h
    · intro h; rw [← hbltu_1, h]; decide
    · intro h; rw [← hbltu_0]; exact h
    · intro h; rw [← hbltu_0, h]; decide

end EvmAsm.Evm64
