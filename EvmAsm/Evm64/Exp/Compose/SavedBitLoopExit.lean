/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopExit

  Named loop-exit boundary assertions for the two-MUL saved-bit EXP
  pointer-restore and epilogue sequence.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulLoopExitPre
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitFullStackPreFrame
    sp evmSp iterCountNew tOld r0 r1 r2 r3 r0 r1 r2 r3
    baseWord rest exitCond

theorem expTwoMulLoopExitPre_unfold
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
      baseWord rest exitCond =
      (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝) **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3))) **
       evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest)) := by
  delta expTwoMulLoopExitPre
  rw [expTwoMulLoopExitFullStackPreFrame_unfold,
    expTwoMulLoopExitControl_unfold]

theorem expTwoMulLoopExitPre_pcFree
    {sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
      baseWord rest exitCond).pcFree := by
  rw [expTwoMulLoopExitPre_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitPre
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
        baseWord rest exitCond) :=
  ⟨expTwoMulLoopExitPre_pcFree⟩

@[irreducible]
def expTwoMulLoopExitPost
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) : Assertion :=
  expTwoMulLoopExitFullStackPostFrame
    sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond

theorem expTwoMulLoopExitPost_unfold
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
      baseWord rest exitCond =
      (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝) **
       ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  delta expTwoMulLoopExitPost
  rw [expTwoMulLoopExitFullStackPostFrame_unfold,
    expTwoMulLoopExitControl_unfold]

/-- Visible-stack view of the named EXP loop-exit post. -/
theorem expTwoMulLoopExitPost_stack_unfold
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
      baseWord rest exitCond =
      (((.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝) **
       ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ (evmSp + 32)) ** (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs evmSp baseWord **
        evmStackIs (evmSp + 32) (expResultWord r0 r1 r2 r3 :: rest))) := by
  unfold expTwoMulLoopExitPost
  rw [expTwoMulLoopExitFullStackPostFrame_stack_unfold, expTwoMulLoopExitControl_unfold]

theorem expTwoMulLoopExitPost_pcFree
    {sp evmSp iterCountNew r0 r1 r2 r3 : Word}
    {baseWord : EvmWord} {rest : List EvmWord} {exitCond : Prop} :
    (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
      baseWord rest exitCond).pcFree := by
  rw [expTwoMulLoopExitPost_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitPost
    (sp evmSp iterCountNew r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop) :
    Assertion.PCFree
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  ⟨expTwoMulLoopExitPost_pcFree⟩

/-- Appended-MUL canonical-code pointer-restore/epilogue boundary with named
    loop-exit pre/post assertions. -/
theorem exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (base : Word) :
    cpsTripleWithin (1 + 9) (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
        baseWord rest exitCond)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) := by
  unfold expTwoMulLoopExitPre expTwoMulLoopExitPost
  simpa [expTwoMulLoopExitFullStackPreFrame_unfold,
    expTwoMulLoopExitFullStackPostFrame_unfold] using
    exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 r0 r1 r2 r3
      baseWord rest exitCond base

/-- Closed-form bound variant of
    `exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_spec_within`. -/
theorem exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_closed_bound_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord) (exitCond : Prop)
    (base : Word) :
    cpsTripleWithin 10 (base + 264) (base + 304)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulLoopExitPre sp evmSp iterCountNew tOld r0 r1 r2 r3
        baseWord rest exitCond)
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord rest exitCond) :=
  exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_exit_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 baseWord rest exitCond base

end EvmAsm.Evm64.Exp.Compose
