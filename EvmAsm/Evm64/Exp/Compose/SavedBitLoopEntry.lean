/-
  EvmAsm.Evm64.Exp.Compose.SavedBitLoopEntry

  Named loop-entry postcondition for the two-MUL saved-bit EXP prologue
  and pointer-advance boundary.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulBoundaryPre
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) : Assertion :=
  (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
      (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
      ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
      ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
      ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
     (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
   expTwoMulScratchFrame vOld v18)

theorem expTwoMulBoundaryPre_unfold_namedScratch
    {sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       expTwoMulScratchFrame vOld v18) := by
  delta expTwoMulBoundaryPre
  rfl

theorem expTwoMulBoundaryPre_unfold
    {sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulBoundaryPre_unfold_namedScratch]
  rw [expTwoMulScratchFrame_unfold]

theorem expTwoMulBoundaryPre_pcFree
    {sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest).pcFree := by
  rw [expTwoMulBoundaryPre_unfold_namedScratch]
  pcFree

instance pcFreeInst_expTwoMulBoundaryPre
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest) :=
  ⟨expTwoMulBoundaryPre_pcFree⟩

@[irreducible]
def expTwoMulLoopEntryPost
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) : Assertion :=
  (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
      (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
      evmWordIs sp (1 : EvmWord)) **
     (.x12 ↦ᵣ (evmSp + 64))) **
   evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
   expTwoMulScratchFrame vOld v18)

theorem expTwoMulLoopEntryPost_unfold_namedScratch
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       expTwoMulScratchFrame vOld v18) := by
  delta expTwoMulLoopEntryPost
  rfl

theorem expTwoMulLoopEntryPost_unfold
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPost_unfold_namedScratch]
  rw [expTwoMulScratchFrame_unfold]

/-- Entry-post unfold that exposes the first two words below the EXP operands.

    After the prologue advances `x12` to `evmSp + 64`, the loop body treats the
    two stack slots below the operands (`dWord`, `eWord`) as squaring/accumulator
    scratch.  This splits the stack assertion into the explicit operand and
    scratch words, the shape the first-iteration precondition `expTwoMulIterPre`
    consumes (non-fixed analog of `expTwoMulLoopEntryPostFixed_unfold_rest2`). -/
theorem expTwoMulLoopEntryPost_unfold_rest2
    {sp evmSp vOld v18 : Word} {baseWord exponentWord dWord eWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPost sp evmSp vOld v18
        baseWord exponentWord (dWord :: eWord :: rest) =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        (evmWordIs evmSp baseWord **
         evmWordIs (evmSp + 32) exponentWord **
         evmWordIs (evmSp + 32 + 32) dWord **
         evmWordIs (evmSp + 32 + 32 + 32) eWord **
         evmStackIs (evmSp + 32 + 32 + 32 + 32) rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPost_unfold]
  rfl

/-- Normalized-offset variant of `expTwoMulLoopEntryPost_unfold_rest2`.
    The first scratch word starts exactly at the advanced iteration stack
    pointer `evmSp + 64`. -/
theorem expTwoMulLoopEntryPost_unfold_rest2_offsets
    {sp evmSp vOld v18 : Word} {baseWord exponentWord dWord eWord : EvmWord}
    {rest : List EvmWord} :
    expTwoMulLoopEntryPost sp evmSp vOld v18
        baseWord exponentWord (dWord :: eWord :: rest) =
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        (evmWordIs evmSp baseWord **
         evmWordIs (evmSp + 32) exponentWord **
         evmWordIs (evmSp + 64) dWord **
         evmWordIs (evmSp + 96) eWord **
         evmStackIs (evmSp + 128) rest)) **
       (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
        (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18))) := by
  rw [expTwoMulLoopEntryPost_unfold_rest2]
  simp only [BitVec.add_assoc,
    show (32 : Word) + 32 = 64 from by decide,
    show (64 : Word) + 32 = 96 from by decide,
    show (96 : Word) + 32 = 128 from by decide]

theorem expTwoMulLoopEntryPost_pcFree
    {sp evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord}
    {rest : List EvmWord} :
    (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest).pcFree := by
  rw [expTwoMulLoopEntryPost_unfold_namedScratch]
  pcFree

instance pcFreeInst_expTwoMulLoopEntryPost
    (sp evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord)
    (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) :=
  ⟨expTwoMulLoopEntryPost_pcFree⟩

/-- Appended-MUL canonical-code prologue/pointer boundary with a named
    loop-entry postcondition. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_entry_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       expTwoMulScratchFrame vOld v18)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) := by
  unfold expTwoMulLoopEntryPost
  exact
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_full_stack_clean_regs_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

/-- Appended-MUL canonical-code prologue/pointer boundary with named pre and
    post assertions. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) := by
  rw [expTwoMulBoundaryPre_unfold_namedScratch]
  exact
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_loop_entry_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

/-- Closed-form bound variant of
    `exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within`. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_closed_bound_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    cpsTripleWithin 7 base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPre sp evmSp cOld tOld m0 m1 m2 m3 vOld v18
        baseWord exponentWord rest)
      (expTwoMulLoopEntryPost sp evmSp vOld v18 baseWord exponentWord rest) :=
  exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_named_boundary_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest base

end EvmAsm.Evm64.Exp.Compose
