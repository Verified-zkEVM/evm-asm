/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologue

  Boundary-block prologue and pointer-advance helpers for the corrected
  two-MUL saved-bit EXP code bundle.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitWithMul
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Rv64.Tactics.XCancelStruct

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

@[irreducible]
def expTwoMulScratchFrame (vOld v18 : Word) : Assertion :=
  regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
  (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)

theorem expTwoMulScratchFrame_unfold {vOld v18 : Word} :
    expTwoMulScratchFrame vOld v18 =
      (regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
       (.x1 ↦ᵣ vOld) ** (.x18 ↦ᵣ v18)) := by
  delta expTwoMulScratchFrame
  rfl

theorem expTwoMulScratchFrame_pcFree {vOld v18 : Word} :
    (expTwoMulScratchFrame vOld v18).pcFree := by
  rw [expTwoMulScratchFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulScratchFrame (vOld v18 : Word) :
    Assertion.PCFree (expTwoMulScratchFrame vOld v18) :=
  ⟨expTwoMulScratchFrame_pcFree⟩

@[irreducible]
def expTwoMulOperandFrame
    (evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord) :
    Assertion :=
  evmWordIs evmSp baseWord ** evmWordIs (evmSp + 32) exponentWord **
  expTwoMulScratchFrame vOld v18

theorem expTwoMulOperandFrame_unfold
    {evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord} :
    expTwoMulOperandFrame evmSp vOld v18 baseWord exponentWord =
      (evmWordIs evmSp baseWord ** evmWordIs (evmSp + 32) exponentWord **
       expTwoMulScratchFrame vOld v18) := by
  delta expTwoMulOperandFrame
  rfl

theorem expTwoMulOperandFrame_pcFree
    {evmSp vOld v18 : Word} {baseWord exponentWord : EvmWord} :
    (expTwoMulOperandFrame evmSp vOld v18 baseWord exponentWord).pcFree := by
  rw [expTwoMulOperandFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulOperandFrame
    (evmSp vOld v18 : Word) (baseWord exponentWord : EvmWord) :
    Assertion.PCFree
      (expTwoMulOperandFrame evmSp vOld v18 baseWord exponentWord) :=
  ⟨expTwoMulOperandFrame_pcFree⟩

theorem expTwoMulBoundaryCounterInitWord :
    ((0 : Word) + signExtend12 (256 : BitVec 12)) = (256 : Word) := by
  rw [EvmAsm.Evm64.Exp.AddrNorm.exp_se12_256]
  bv_omega

theorem expTwoMulBoundaryAccumulatorInitWord :
    ((0 : Word) + signExtend12 (1 : BitVec 12)) = (1 : Word) := by
  rw [signExtend12_1]
  bv_omega

theorem expTwoMulBoundaryAdvancedEvmSpWord (evmSp : Word) :
    evmSp + signExtend12 (64 : BitVec 12) = evmSp + 64 := by
  rw [signExtend12_64]

theorem expTwoMulPointerRestoreBackToEvmSp (evmSp : Word) :
    (evmSp + signExtend12 (64 : BitVec 12)) +
      signExtend12 ((-64) : BitVec 12) = evmSp := by
  rw [signExtend12_64, EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]
  bv_omega

theorem expTwoMulBoundaryResultEvmSpWord (evmSp : Word) :
    evmSp + signExtend12 (32 : BitVec 12) = evmSp + 32 := by
  rw [signExtend12_32]

theorem expTwoMulBoundaryResultTailWord (evmSp : Word) :
    evmSp + 32 + 32 = evmSp + 64#64 := by
  bv_addr

theorem expTwoMulBoundaryResultTailWord_symm (evmSp : Word) :
    evmSp + 64 = evmSp + 32#64 + 32#64 := by
  bv_addr

theorem expTwoMulBoundaryResultTailWord_symm_word (evmSp : Word) :
    evmSp + 64#64 = evmSp + 32 + 32 := by
  bv_addr

@[irreducible]
def expTwoMulLoopExitStackTailFrame
    (evmSp : Word) (baseWord : EvmWord) (rest : List EvmWord) :
    Assertion :=
  evmWordIs evmSp baseWord ** evmStackIs (evmSp + 64) rest

theorem expTwoMulLoopExitStackTailFrame_unfold
    {evmSp : Word} {baseWord : EvmWord} {rest : List EvmWord} :
    expTwoMulLoopExitStackTailFrame evmSp baseWord rest =
      (evmWordIs evmSp baseWord ** evmStackIs (evmSp + 64) rest) := by
  delta expTwoMulLoopExitStackTailFrame
  rfl

theorem expTwoMulLoopExitStackTailFrame_pcFree
    {evmSp : Word} {baseWord : EvmWord} {rest : List EvmWord} :
    (expTwoMulLoopExitStackTailFrame evmSp baseWord rest).pcFree := by
  rw [expTwoMulLoopExitStackTailFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulLoopExitStackTailFrame
    (evmSp : Word) (baseWord : EvmWord) (rest : List EvmWord) :
    Assertion.PCFree
      (expTwoMulLoopExitStackTailFrame evmSp baseWord rest) :=
  ⟨expTwoMulLoopExitStackTailFrame_pcFree⟩

/-- EXP prologue followed by the pointer-advance block, lifted to the
    two-MUL saved-bit EXP+MUL code bundle. This lands at the iteration-body
    entry with the EVM stack pointer advanced by one operand window. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
        (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
       (.x12 ↦ᵣ evmSp))
      (((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
        (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
        evmWordIs sp (1 : EvmWord)) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) := by
  have hPrologue :=
    exp_prologue_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPrologueFramed :=
    cpsTripleWithin_frameR (.x12 ↦ᵣ evmSp) (by pcFree) hPrologue
  have hPointer :=
    exp_loop_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      evmSp squaringMulOff condMulOff skipOff backOff base mulTarget
  have hPointerFramed :=
    cpsTripleWithin_frameR
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
       (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
       (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
       evmWordIs sp (1 : EvmWord))
      (by pcFree)
      hPointer
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by xperm_hyp hp)
      hPrologueFramed hPointerFramed
  exact cpsTripleWithin_weaken
    (fun _ hp => by xperm_hyp hp)
    (fun _ hp => by xperm_hyp hp)
    hSeq

/-- Stack-operand framed view of the two-MUL saved-bit EXP prologue followed
    by pointer advance. This preserves the visible EVM operand windows and
    caller-saved scratch ownership while the accumulator is initialized to one
    and `x12` advances to the loop-facing pointer. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_operand_frame_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let operandFrame : Assertion :=
      expTwoMulOperandFrame evmSp vOld v18 baseWord exponentWord
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
         (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
        (.x12 ↦ᵣ evmSp)) ** operandFrame)
      ((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
         (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
         (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
         evmWordIs sp (1 : EvmWord)) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) ** operandFrame) := by
  intro operandFrame
  have hBase :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR operandFrame (by pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      rw [expTwoMulOperandFrame_unfold, expTwoMulScratchFrame_unfold] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [operandFrame] at hp ⊢
      rw [expTwoMulOperandFrame_unfold, expTwoMulScratchFrame_unfold] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Full visible-stack framed view of the two-MUL saved-bit EXP prologue
    followed by pointer advance. This folds the preserved base/exponent
    operands together with the untouched caller tail, while the accumulator is
    initialized to one and `x12` advances to the loop-facing pointer. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_frame_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      expTwoMulScratchFrame vOld v18
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ ((0 : Word) + signExtend12 (256 : BitVec 12))) **
          (.x5 ↦ᵣ ((0 : Word) + signExtend12 (1 : BitVec 12))) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12)))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  intro scratchFrame
  let operandFrame : Assertion :=
    expTwoMulOperandFrame evmSp vOld v18 baseWord exponentWord
  have hBase :=
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_operand_frame_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR (evmStackIs (evmSp + 64) rest)
    pcFree_evmStackIs hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [scratchFrame, operandFrame] at hp ⊢
      rw [expTwoMulOperandFrame_unfold]
      rw [expTwoMulScratchFrame_unfold] at hp ⊢
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [expTwoMulBoundaryResultTailWord] at hp
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [scratchFrame, operandFrame] at hp ⊢
      rw [expTwoMulOperandFrame_unfold] at hp
      rw [expTwoMulScratchFrame_unfold] at hp ⊢
      rw [evmStackIs_cons, evmStackIs_cons]
      rw [expTwoMulBoundaryResultTailWord_symm_word] at hp
      xperm_hyp hp)
    hFramed

/-- Consumer-facing version of the full-stack prologue/pointer-advance view:
    expose the initialized loop counter, accumulator temp, and advanced EVM
    stack pointer as plain word constants. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      expTwoMulScratchFrame vOld v18
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  intro scratchFrame
  exact cpsTripleWithin_weaken
    (fun _ hp => hp)
    (fun _ hp => by
      rw [expTwoMulBoundaryCounterInitWord] at hp
      rw [expTwoMulBoundaryAccumulatorInitWord] at hp
      rw [expTwoMulBoundaryAdvancedEvmSpWord] at hp
      exact hp)
    (exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_frame_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Canonical-code view of the full-stack prologue/pointer-advance boundary:
    the branch offsets are fixed by `evmExpMsbSavedBitTwoMulCanonicalWithMulCode`,
    while the two external MUL-call offsets remain caller supplied. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    let scratchFrame : Assertion :=
      expTwoMulScratchFrame vOld v18
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) := by
  exact
    exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_with_mul_full_stack_clean_regs_spec_within
      sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitLoopBackOff
      base mulTarget

/-- Appended-MUL canonical-code view of the full-stack
    prologue/pointer-advance boundary. -/
theorem exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_appended_mul_full_stack_clean_regs_spec_within
    (sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    let scratchFrame : Assertion :=
      expTwoMulScratchFrame vOld v18
    cpsTripleWithin (6 + 1) base (base + 28)
      (evmExpMsbSavedBitTwoMulCanonicalAppendedMulCode base)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
          (.x5 ↦ᵣ tOld) ** ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3)) **
         (.x12 ↦ᵣ evmSp)) ** evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame)
      (((((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) **
          (.x9 ↦ᵣ (256 : Word)) ** (.x5 ↦ᵣ (1 : Word)) **
          evmWordIs sp (1 : EvmWord)) **
         (.x12 ↦ᵣ (evmSp + 64))) **
        evmStackIs evmSp (baseWord :: exponentWord :: rest)) **
       scratchFrame) :=
  exp_prologue_then_pointer_advance_evm_exp_msb_saved_bit_two_mul_canonical_with_mul_full_stack_clean_regs_spec_within
    sp evmSp cOld tOld m0 m1 m2 m3 vOld v18 baseWord exponentWord rest
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base (base + 304)

end EvmAsm.Evm64.Exp.Compose
