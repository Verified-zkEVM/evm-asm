/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul

  Code-bundle helpers for the fixed x19 two-MUL saved-bit EXP program plus
  the out-of-line `mul_callable` body.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryPrologueFixed
import EvmAsm.Evm64.Exp.Compose.SavedBitIterPostDefs
import EvmAsm.Evm64.Exp.Compose.SavedBitBaseTwoMulFixedIterMerged
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundarySeq

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64.Tactics
open EvmAsm.Rv64

/-- Fixed saved-bit EXP code plus the external `mul_callable` body reached by
    both JALs in one loop iteration. -/
abbrev evmExpMsbSavedBitTwoMulFixedWithMulCode (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) : CodeReq :=
  (expMsbSavedBitTwoMulFixedCode
    base squaringMulOff condMulOff skipOff backOff).union
    (mul_callable_code mulTarget)

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13} :
    ∀ a i, (expMsbSavedBitTwoMulFixedCode
      base squaringMulOff condMulOff skipOff backOff) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.union_mono_left

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_mul_sub {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, (mul_callable_code mulTarget) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.mono_union_right hd (fun _ _ h => h)

/-- Lift a whole fixed-EXP triple spec into the fixed EXP+MUL code bundle. -/
theorem cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_ base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q : Assertion}
    (h : cpsTripleWithin nSteps entry exit_
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) P Q) :
    cpsTripleWithin nSteps entry exit_
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P Q :=
  cpsTripleWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

/-- Lift a whole fixed-EXP branch spec into the fixed EXP+MUL code bundle. -/
theorem cpsBranchWithin_extend_fixedCode_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_t exit_f base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q_t Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

/-- Lift a whole fixed-EXP N-branch spec into the fixed EXP+MUL code bundle. -/
theorem cpsNBranchWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff) P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) P exits :=
  cpsNBranchWithin_extend_code
    (hmono := evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub) h

/-- Fixed full-stack prologue + pointer advance lifted into the fixed EXP+MUL
    code bundle used by loop-body proofs. -/
theorem exp_prologue_fixed_then_pointer_advance_full_stack_evmExpMsbSavedBitTwoMulFixedWithMulCode_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18 : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (10 + 1) base (base + 44)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x0 ↦ᵣ (0 : Word)) ** (.x9 ↦ᵣ cOld) **
       (.x5 ↦ᵣ tOld) ** (.x12 ↦ᵣ evmSp) **
       (.x20 ↦ᵣ c6Old) ** (.x16 ↦ᵣ c16Old) ** (.x19 ↦ᵣ c19Old) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ m0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ m1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ m2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ m3) **
       expTwoMulScratchFrame vOld v18 **
       evmStackIs evmSp (baseWord :: exponentWord :: rest))
      (expTwoMulLoopEntryPostFixed sp evmSp vOld v18 baseWord exponentWord rest) :=
  cpsTripleWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    (mulTarget := mulTarget)
    (exp_prologue_fixed_then_pointer_advance_full_stack_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old m0 m1 m2 m3 vOld v18
      baseWord exponentWord rest squaringMulOff condMulOff skipOff backOff base)

/-- Fixed pointer restore lifted to the fixed EXP+MUL code bundle. -/
theorem exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (vOld : Word) (squaringMulOff condMulOff : BitVec 21)
    (skipOff backOff : BitVec 13) (base mulTarget : Word) :
    cpsTripleWithin 1 (base + 296) (base + 300)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (.x12 ↦ᵣ vOld)
      (.x12 ↦ᵣ (vOld + signExtend12 ((-64) : BitVec 12))) := by
  have h := EvmAsm.Evm64.exp_loop_pointer_restore_spec_within vOld (base + 296)
  have haddr : (base + 296 : Word) + 4 = base + 300 := by bv_addr
  rw [haddr] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i h =>
      evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub a i
        (expMsbSavedBitTwoMulFixedCode_pointer_restore_sub a i h))

/-- Fixed EXP epilogue lifted to the fixed EXP+MUL code bundle. -/
theorem exp_epilogue_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin 9 (base + 300) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
       ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
       ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
       ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  have h := EvmAsm.Evm64.exp_epilogue_word_spec_within
    sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 (base + 300)
  have haddr : (base + 300 : Word) + 36 = base + 336 := by bv_addr
  rw [haddr] at h
  exact cpsTripleWithin_extend_code
    (h := h)
    (hmono := fun a i h =>
      evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub a i
        (expMsbSavedBitTwoMulFixedCode_epilogue_sub a i h))

/-- Fixed pointer restore followed by the EXP epilogue over the fixed EXP+MUL
    code bundle. -/
theorem exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
       ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))
      ((.x2 ↦ᵣ sp) **
       (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
       (.x5 ↦ᵣ r3) **
       ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
       ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
       ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
       ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
       evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3)) := by
  let epilogueFrame : Assertion :=
    (.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)
  have hRestore :=
    exp_loop_pointer_restore_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      (evmSp + signExtend12 (64 : BitVec 12))
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hRestoreFramed := cpsTripleWithin_frameR epilogueFrame (by
    dsimp [epilogueFrame]
    pcFree) hRestore
  have hPtr : (evmSp + signExtend12 (64 : BitVec 12)) +
      signExtend12 ((-64) : BitVec 12) = evmSp := by
    rw [signExtend12_64, EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64]
    bv_omega
  have hRestoreFramed' :
      cpsTripleWithin 1 (base + 296) (base + 300)
        (evmExpMsbSavedBitTwoMulFixedWithMulCode
          base mulTarget squaringMulOff condMulOff skipOff backOff)
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) ** epilogueFrame)
        ((.x12 ↦ᵣ evmSp) ** epilogueFrame) := by
    rw [hPtr] at hRestoreFramed
    exact hRestoreFramed
  have hEpilogue :=
    exp_epilogue_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hSeq :=
    cpsTripleWithin_seq_perm_same_cr
      (fun _ hp => by
        dsimp [epilogueFrame] at hp ⊢
        xperm_hyp hp)
      hRestoreFramed' hEpilogue
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [epilogueFrame] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => hp)
    hSeq

/-- Exit-control framed view of the fixed pointer-restore/epilogue sequence. -/
theorem exp_pointer_restore_then_epilogue_exit_control_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (exitControl **
       ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
        ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
         ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
         ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
         ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
         ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
         ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
         ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
         ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
         ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3))))
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs (evmSp + 32) (expResultWord r0 r1 r2 r3))) := by
  intro exitControl
  have hBase :=
    exp_pointer_restore_then_epilogue_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp tOld r0 r1 r2 r3 d0 d1 d2 d3
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameL exitControl (by
    dsimp [exitControl]
    pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [exitControl] at hp ⊢
      xperm_hyp hp)
    hFramed

/-- Stack-tail framed view of the fixed pointer-restore/epilogue sequence. -/
theorem exp_pointer_restore_then_epilogue_stack_tail_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmWordIs evmSp baseWord **
        evmStackIs (evmSp + 32) (expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  have hBase :=
    exp_pointer_restore_then_epilogue_exit_control_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget
  have hFramed := cpsTripleWithin_frameR stackTail (by pcFree) hBase
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp ⊢
      xperm_hyp hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [expTwoMulLoopExitStackTailFrame_unfold] at hp
      rw [evmStackIs_cons]
      rw [show evmSp + 64 = evmSp + 32#64 + 32#64 from by bv_addr] at hp
      xperm_hyp hp)
    hFramed

/-- Fixed pointer-restore/epilogue view with the visible post stack folded. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + signExtend12 (32 : BitVec 12))) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      exact hp)
    (fun _ hp => by
      dsimp [exitControl, stackTail] at hp ⊢
      rw [evmStackIs_cons]
      xperm_hyp hp)
    (exp_pointer_restore_then_epilogue_stack_tail_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

/-- Fixed full visible-post-stack view with the final EVM stack pointer exposed
    in plain consumer-facing form. -/
theorem exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    let exitControl : Assertion :=
      (.x9 ↦ᵣ iterCountNew) ** (.x0 ↦ᵣ (0 : Word)) ** ⌜exitCond⌝
    let stackTail : Assertion :=
      expTwoMulLoopExitStackTailFrame evmSp baseWord rest
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      ((exitControl **
        ((.x12 ↦ᵣ (evmSp + signExtend12 (64 : BitVec 12))) **
         ((.x2 ↦ᵣ sp) ** (.x5 ↦ᵣ tOld) **
          ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
          ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
          ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
          ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
          ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ d0) **
          ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ d1) **
          ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ d2) **
          ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ d3)))) **
       stackTail)
      (exitControl **
       ((.x2 ↦ᵣ sp) **
        (.x12 ↦ᵣ (evmSp + 32)) **
        (.x5 ↦ᵣ r3) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        evmStackIs evmSp (baseWord :: expResultWord r0 r1 r2 r3 :: rest))) := by
  intro exitControl stackTail
  rw [← expTwoMulBoundaryResultEvmSpWord]
  exact exp_pointer_restore_then_epilogue_full_post_stack_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    squaringMulOff condMulOff skipOff backOff base mulTarget

/-- Full visible-stack view of the fixed pointer-restore/epilogue sequence. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21) (skipOff backOff : BitVec 13)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) := by
  exact cpsTripleWithin_weaken
    (fun _ hp => by
      rw [expTwoMulLoopExitFullStackPreFrame_unfold] at hp
      rw [expTwoMulLoopExitControl_unfold] at hp
      rw [evmStackIs_cons, evmStackIs_cons] at hp
      rw [← exp_epilogue_result_word_right evmSp d0 d1 d2 d3
        (evmStackIs (evmSp + 32 + 32) rest)] at hp
      rw [expTwoMulBoundaryResultTailWord] at hp
      rw [expTwoMulLoopExitStackTailFrame_unfold]
      xcancel_struct hp)
    (fun _ hp => by
      rw [expTwoMulLoopExitFullStackPostFrame_unfold]
      rw [expTwoMulLoopExitControl_unfold]
      exact hp)
    (exp_pointer_restore_then_epilogue_full_post_stack_clean_pointer_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff skipOff backOff base mulTarget)

theorem evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
    {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    ∀ a i, ((expIterBodyFullMsbSavedBitTwoMulFixedCode
      (base + 44) squaringMulOff condMulOff skipOff backOff).union
      (mul_callable_code mulTarget)) a = some i →
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff) a = some i := by
  exact CodeReq.union_sub
    (fun a i h =>
      evmExpMsbSavedBitTwoMulFixedWithMulCode_exp_sub a i
        (expMsbSavedBitTwoMulFixedCode_iter_body_sub a i
          (expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg
            (base + 44) squaringMulOff condMulOff skipOff backOff ▸ h)))
    (evmExpMsbSavedBitTwoMulFixedWithMulCode_mul_sub hd)

theorem expIterBodyFullMsbSavedBitTwoMulFixedCode_disjoint_mul_of_fixed_disjoint
    {base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget)) :
    CodeReq.Disjoint
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget) := by
  intro a
  rcases hd a with h_fixed | h_mul
  · left
    cases h_body :
        (expIterBodyFullMsbSavedBitTwoMulFixedCode
          (base + 44) squaringMulOff condMulOff skipOff backOff) a with
    | none => rfl
    | some i =>
        have h_sub := expMsbSavedBitTwoMulFixedCode_iter_body_sub a i
          (expIterBodyFullMsbSavedBitTwoMulFixedCode_eq_ofProg
            (base + 44) squaringMulOff condMulOff skipOff backOff ▸ h_body)
        rw [h_fixed] at h_sub
        contradiction
  · right
    exact h_mul

/-- Lift a fixed iteration-body branch spec into the whole fixed EXP+MUL code
    bundle. The fixed iteration body starts 44 bytes after the fixed EXP entry. -/
theorem cpsBranchWithin_extend_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry exit_t exit_f base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P Q_t Q_f : Assertion}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsBranchWithin nSteps entry
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (h := h)
    (hmono :=
      evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
        (base := base) (mulTarget := mulTarget)
        (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
        (skipOff := skipOff) (backOff := backOff) hd)

/-- Fixed saved-bit EXP with canonical internal branch offsets plus an external
    `mul_callable` target. -/
abbrev evmExpMsbSavedBitTwoMulFixedCanonicalWithMulCode
    (base mulTarget : Word)
    (squaringMulOff condMulOff : BitVec 21) : CodeReq :=
  evmExpMsbSavedBitTwoMulFixedWithMulCode
    base mulTarget squaringMulOff condMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff

/-- Fixed saved-bit EXP with canonical internal branches and appended
    `mul_callable` immediately after the 336-byte fixed EXP wrapper. -/
abbrev evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    (base : Word) : CodeReq :=
  evmExpMsbSavedBitTwoMulFixedCanonicalWithMulCode
    base (base + 336)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff

/-- Fixed canonical iteration-body code plus the appended `mul_callable`, as
    it sits inside the full 336-byte fixed EXP wrapper. -/
abbrev expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    (base : Word) : CodeReq :=
  (expIterBodyFullMsbSavedBitTwoMulFixedCode
    (base + 44)
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    EvmAsm.Evm64.canonicalExpCondMulSkipOff
    EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).union
    (mul_callable_code (base + 336))

theorem expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq
    (base : Word) :
    expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base =
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44)
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff).union
        (mul_callable_code (base + 336)) := rfl

@[irreducible]
def expTwoMulFixedIterPointerFrame (ptr nextLimb : Word) : Assertion :=
  (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)

theorem expTwoMulFixedIterPointerFrame_unfold {ptr nextLimb : Word} :
    expTwoMulFixedIterPointerFrame ptr nextLimb =
      ((.x16 ↦ᵣ ptr) **
       ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) := by
  delta expTwoMulFixedIterPointerFrame
  rfl

theorem expTwoMulFixedIterPointerFrame_pcFree {ptr nextLimb : Word} :
    (expTwoMulFixedIterPointerFrame ptr nextLimb).pcFree := by
  rw [expTwoMulFixedIterPointerFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterPointerFrame (ptr nextLimb : Word) :
    Assertion.PCFree (expTwoMulFixedIterPointerFrame ptr nextLimb) :=
  ⟨expTwoMulFixedIterPointerFrame_pcFree⟩

@[irreducible]
def expTwoMulFixedIterPre
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) : Assertion :=
  ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** regOwn .x6 ** (.x10 ↦ᵣ v10) **
    (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
    (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
    ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
    ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
    ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
    ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
    ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
    ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
    ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
    ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
    ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
    ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
    ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
    ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
    (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
    (.x9 ↦ᵣ iterCount)) ** expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)) **
    expTwoMulFixedIterPointerFrame ptr nextLimb)

theorem expTwoMulFixedIterPre_unfold
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
      vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 =
      ((((((.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** regOwn .x6 ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld)) **
        (.x9 ↦ᵣ iterCount)) ** expTwoMulIterBaseFrame evmSp a0 a1 a2 a3)) **
        expTwoMulFixedIterPointerFrame ptr nextLimb) := by
  delta expTwoMulFixedIterPre
  rfl

theorem expTwoMulFixedIterPre_pcFree
    {e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word} :
    (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
      vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11).pcFree := by
  rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
    expTwoMulFixedIterPointerFrame_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterPre
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld
        vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3 v7 v11) :=
  ⟨expTwoMulFixedIterPre_pcFree⟩

/-- Canonical-code view of the fixed loop-exit boundary: pointer restore
    followed by EXP epilogue over fixed EXP+MUL code. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_with_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (squaringMulOff condMulOff : BitVec 21)
    (base mulTarget : Word) :
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalWithMulCode
        base mulTarget squaringMulOff condMulOff)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) := by
  exact
    exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_with_mul_spec_within
      sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
      squaringMulOff condMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
      base mulTarget

/-- Appended-MUL canonical-code view of the fixed loop-exit boundary. -/
theorem exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_appended_mul_spec_within
    (sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop)
    (base : Word) :
    cpsTripleWithin (1 + 9) (base + 296) (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulLoopExitFullStackPreFrame
        sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3
        baseWord rest exitCond)
      (expTwoMulLoopExitFullStackPostFrame
        sp evmSp iterCountNew r0 r1 r2 r3 baseWord rest exitCond) :=
  exp_pointer_restore_then_epilogue_full_stack_evm_exp_msb_saved_bit_two_mul_fixed_canonical_with_mul_spec_within
    sp evmSp iterCountNew tOld r0 r1 r2 r3 d0 d1 d2 d3 baseWord rest exitCond
    EvmAsm.Evm64.canonicalExpSquaringMulOff
    EvmAsm.Evm64.canonicalExpCondMulOff
    base (base + 336)

/-- Lift a fixed iteration-body N-branch spec into the whole fixed EXP+MUL
    code bundle. -/
theorem cpsNBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedWithMulCode
    {nSteps : Nat} {entry base mulTarget : Word}
    {squaringMulOff condMulOff : BitVec 21} {skipOff backOff : BitVec 13}
    {P : Assertion} {exits : List (Word × Assertion)}
    (hd : CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base squaringMulOff condMulOff skipOff backOff)
      (mul_callable_code mulTarget))
    (h : cpsNBranchWithin nSteps entry
      ((expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44) squaringMulOff condMulOff skipOff backOff).union
        (mul_callable_code mulTarget))
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedWithMulCode
        base mulTarget squaringMulOff condMulOff skipOff backOff)
      P exits :=
  cpsNBranchWithin_extend_code
    (h := h)
    (hmono :=
      evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
        (base := base) (mulTarget := mulTarget)
        (squaringMulOff := squaringMulOff) (condMulOff := condMulOff)
        (skipOff := skipOff) (backOff := backOff) hd)

/-- The fixed canonical saved-bit EXP wrapper is disjoint from a `mul_callable`
    body appended immediately after the 336-byte wrapper. -/
theorem expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul
    (base : Word) :
    CodeReq.Disjoint
      (expMsbSavedBitTwoMulFixedCode
        base EvmAsm.Evm64.canonicalExpSquaringMulOff
          EvmAsm.Evm64.canonicalExpCondMulOff
          EvmAsm.Evm64.canonicalExpCondMulSkipOff
          EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (mul_callable_code (base + 336)) := by
  unfold expMsbSavedBitTwoMulFixedCode
  rw [mul_callable_code_eq_ofProg]
  exact CodeReq.ofProg_disjoint_range_len
    base
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
    84
    (base + 336)
    EvmAsm.Evm64.mul_callable
    64
    (EvmAsm.Evm64.evm_exp_msb_saved_bit_two_mul_fixed_length
      EvmAsm.Evm64.canonicalExpSquaringMulOff
      EvmAsm.Evm64.canonicalExpCondMulOff
      EvmAsm.Evm64.canonicalExpCondMulSkipOff
      EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
    EvmAsm.Evm64.mul_callable_length
    (fun _ _ hk1 hk2 => by bv_omega)

theorem evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_mul_sub
    {base : Word} :
    ∀ a i, (mul_callable_code (base + 336)) a = some i →
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base) a = some i := by
  unfold evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    evmExpMsbSavedBitTwoMulFixedCanonicalWithMulCode
    evmExpMsbSavedBitTwoMulFixedWithMulCode
  exact CodeReq.mono_union_right
    (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
    (fun _ _ h => h)

theorem expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub
    {base : Word} :
    ∀ a i,
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        a = some i →
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base) a = some i := by
  rw [expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq]
  exact
    evmExpMsbSavedBitTwoMulFixedWithMulCode_iter_body_union_mul_sub
      (base := base) (mulTarget := base + 336)
      (squaringMulOff := EvmAsm.Evm64.canonicalExpSquaringMulOff)
      (condMulOff := EvmAsm.Evm64.canonicalExpCondMulOff)
      (skipOff := EvmAsm.Evm64.canonicalExpCondMulSkipOff)
      (backOff := EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)

/-- Lift a fixed canonical iteration-body branch spec plus appended
    `mul_callable` into the whole fixed canonical appended EXP+MUL code. -/
theorem cpsBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    {nSteps : Nat} {entry exit_t exit_f base : Word}
    {P Q_t Q_f : Assertion}
    (h : cpsBranchWithin nSteps entry
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exit_t Q_t exit_f Q_f) :
    cpsBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exit_t Q_t exit_f Q_f :=
  cpsBranchWithin_extend_code
    (h := h)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub)

/-- Lift a fixed canonical iteration-body N-branch spec plus appended
    `mul_callable` into the whole fixed canonical appended EXP+MUL code. -/
theorem cpsNBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
    {nSteps : Nat} {entry base : Word}
    {P : Assertion} {exits : List (Word × Assertion)}
    (h : cpsNBranchWithin nSteps entry
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exits) :
    cpsNBranchWithin nSteps entry
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      P exits :=
  cpsNBranchWithin_extend_code
    (h := h)
    (hmono := expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_sub)

/-- The fixed canonical iteration body inside the 336-byte wrapper is disjoint
    from the appended `mul_callable` body. -/
theorem expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul
    (base : Word) :
    CodeReq.Disjoint
      (expIterBodyFullMsbSavedBitTwoMulFixedCode
        (base + 44)
        EvmAsm.Evm64.canonicalExpSquaringMulOff
        EvmAsm.Evm64.canonicalExpCondMulOff
        EvmAsm.Evm64.canonicalExpCondMulSkipOff
        EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff)
      (mul_callable_code (base + 336)) :=
  expIterBodyFullMsbSavedBitTwoMulFixedCode_disjoint_mul_of_fixed_disjoint
    (expMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)

/-- Canonical-appended whole-code view of the fixed x19 merged full-iteration
    branch. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    let skipCondFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let skipCondRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    let reloadCondFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let reloadSkipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let reloadCondRest : Assertion := skipCondRest
    let skipLoopPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let skipExitPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let reloadLoopPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
    let reloadExitPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (fun h => skipLoopPost h ∨ reloadLoopPost h)
      (base + 296)
      (fun h => skipExitPost h ∨ reloadExitPost h) := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
        expTwoMulFixedIterPointerFrame_unfold] at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P :=
        (.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x9 ↦ᵣ iterCount) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      (fun v6 => by
        have h :=
          exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
            e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
            r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
            v7 v11 (base + 336) (base + 44)
            EvmAsm.Evm64.canonicalExpSquaringMulOff
            EvmAsm.Evm64.canonicalExpCondMulOff
            EvmAsm.Evm64.canonicalExpCondMulSkipOff
            EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
            (base + 44) hbase
            (EvmAsm.Evm64.canonicalExpFixedSquaringMul_target base).symm
            (EvmAsm.Evm64.canonicalExpFixedCondMul_target base).symm
            (EvmAsm.Evm64.canonicalExpFixedCondMulSkip_target base)
            (EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBack_target base)
            (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
        rw [hExit] at h
        rw [← expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq base] at h
        have h' :=
          cpsBranchWithin_extend_iter_body_union_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode
            h
        refine cpsBranchWithin_weaken ?_ (fun _ hp => hp) (fun _ hp => hp) h'
        intro st hp
        dsimp only [] at hp ⊢
        xperm_hyp hp))

/-- N-branch view of the canonical-appended whole-code fixed x19 merged
    full-iteration spec. -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    let skipCondFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let skipCondRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    let reloadCondFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let reloadSkipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let reloadCondRest : Assertion := skipCondRest
    let skipLoopPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let skipExitPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let reloadLoopPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
    let reloadExitPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      [((base + 44), (fun h => skipLoopPost h ∨ reloadLoopPost h)),
       ((base + 296), (fun h => skipExitPost h ∨ reloadExitPost h))] := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  exact cpsBranchWithin_as_cpsNBranchWithin
    (exp_msb_bit_test_fixed_full_iter_merged_exit_branch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)


/-- Body-only-code-req twin of the merged-exit BRANCH spec (path A, bug fjivz). -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    let skipCondFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let skipCondRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    let reloadCondFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let reloadSkipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let reloadCondRest : Assertion := skipCondRest
    let skipLoopPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let skipExitPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let reloadLoopPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
    let reloadExitPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
    cpsBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      (base + 44)
      (fun h => skipLoopPost h ∨ reloadLoopPost h)
      (base + 296)
      (fun h => skipExitPost h ∨ reloadExitPost h) := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  have hExit : ((base + 44) + 252 : Word) = base + 296 := by bv_addr
  refine cpsBranchWithin_weaken
    (fun _ hp => by
      rw [expTwoMulFixedIterPre_unfold, expTwoMulIterBaseFrame_unfold,
        expTwoMulFixedIterPointerFrame_unfold] at hp
      xperm_hyp hp)
    (fun _ hp => hp) (fun _ hp => hp)
    (cpsBranchWithin_of_forall_regIs_to_regOwn (r := .x6)
      (P :=
        (.x19 ↦ᵣ e) ** (.x20 ↦ᵣ c6) ** (.x10 ↦ᵣ v10) **
        (.x18 ↦ᵣ v18) ** (.x0 ↦ᵣ (0 : Word)) **
        (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) ** (.x5 ↦ᵣ tOld) **
        ((sp + signExtend12 (0 : BitVec 12)) ↦ₘ r0) **
        ((sp + signExtend12 (8 : BitVec 12)) ↦ₘ r1) **
        ((sp + signExtend12 (16 : BitVec 12)) ↦ₘ r2) **
        ((sp + signExtend12 (24 : BitVec 12)) ↦ₘ r3) **
        ((evmSp + signExtend12 (0 : BitVec 12)) ↦ₘ d0) **
        ((evmSp + signExtend12 (8 : BitVec 12)) ↦ₘ d1) **
        ((evmSp + signExtend12 (16 : BitVec 12)) ↦ₘ d2) **
        ((evmSp + signExtend12 (24 : BitVec 12)) ↦ₘ d3) **
        ((evmSp + signExtend12 (32 : BitVec 12)) ↦ₘ e0) **
        ((evmSp + signExtend12 (40 : BitVec 12)) ↦ₘ e1) **
        ((evmSp + signExtend12 (48 : BitVec 12)) ↦ₘ e2) **
        ((evmSp + signExtend12 (56 : BitVec 12)) ↦ₘ e3) **
        (.x7 ↦ᵣ v7) ** (.x11 ↦ᵣ v11) ** (.x1 ↦ᵣ vOld) **
        (.x9 ↦ᵣ iterCount) **
        ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
        ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
        ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
        ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
        (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb))
      (fun v6 => by
        have h :=
          exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCode_spec_within
            e c6 v6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
            r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
            v7 v11 (base + 336) (base + 44)
            EvmAsm.Evm64.canonicalExpSquaringMulOff
            EvmAsm.Evm64.canonicalExpCondMulOff
            EvmAsm.Evm64.canonicalExpCondMulSkipOff
            EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBackOff
            (base + 44) hbase
            (EvmAsm.Evm64.canonicalExpFixedSquaringMul_target base).symm
            (EvmAsm.Evm64.canonicalExpFixedCondMul_target base).symm
            (EvmAsm.Evm64.canonicalExpFixedCondMulSkip_target base)
            (EvmAsm.Evm64.canonicalExpMsbSavedBitFixedLoopBack_target base)
            (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalCode_disjoint_appended_mul base)
        rw [hExit] at h
        rw [← expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_eq base] at h
        refine cpsBranchWithin_weaken ?_ (fun _ hp => hp) (fun _ hp => hp) h
        intro st hp
        dsimp only [] at hp ⊢
        xperm_hyp hp))

/-- Body-only-code-req twin of the merged-exit NBRANCH spec (path A, bug fjivz). -/
theorem exp_msb_bit_test_fixed_full_iter_merged_exit_nbranch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
    (e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0) :
    let bit := e >>> (63 : BitVec 6).toNat
    let c6New := c6 + signExtend12 (-1 : BitVec 12)
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    let baseFrame : Assertion :=
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3)
    let ptrFrame : Assertion :=
      (.x16 ↦ᵣ ptr) ** ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)
    let skipCondFrame : Assertion :=
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let skipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ (e <<< (1 : BitVec 6).toNat)) **
      (.x20 ↦ᵣ c6New) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New ≠ 0⌝ ** ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let skipCondRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ rw.getLimbN 3) **
      ((evmSp + signExtend12 ((-64) : BitVec 12)) ↦ₘ a0) **
      ((evmSp + signExtend12 ((-56) : BitVec 12)) ↦ₘ a1) **
      ((evmSp + signExtend12 ((-48) : BitVec 12)) ↦ₘ a2) **
      ((evmSp + signExtend12 ((-40) : BitVec 12)) ↦ₘ a3) **
      evmWordIs sp rw ** evmWordIs (evmSp + 32) rw **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 140) + 68))
    let reloadCondFrame : Assertion :=
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) ≠ 0⌝
    let reloadSkipRest : Assertion :=
      (.x2 ↦ᵣ sp) ** (.x12 ↦ᵣ evmSp) **
      (.x5 ↦ᵣ squareW.getLimbN 3) **
      evmWordIs sp squareW ** evmWordIs (evmSp + 32) squareW **
      regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11 **
      memOwn evmSp ** memOwn (evmSp + 8) **
      memOwn (evmSp + 16) ** memOwn (evmSp + 24) **
      (.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ (bit + signExtend12 (0 : BitVec 12))) **
      ⌜c6New = 0⌝ **
      (.x16 ↦ᵣ (ptr + signExtend12 (-8 : BitVec 12))) **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
      ⌜bit + signExtend12 (0 : BitVec 12) = 0⌝
    let reloadCondRest : Assertion := skipCondRest
    let skipLoopPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let skipExitPost : Assertion :=
      (fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipCondRest) ** skipCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** skipRest) ** baseFrame) h) **
        ptrFrame
    let reloadLoopPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount ≠ 0⌝) ** reloadSkipRest) ** baseFrame) h
    let reloadExitPost : Assertion :=
      fun h =>
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadCondRest) ** reloadCondFrame) h ∨
        ((((.x9 ↦ᵣ expTwoMulIterCountNew iterCount) ** (.x0 ↦ᵣ (0 : Word)) **
          ⌜expTwoMulIterCountNew iterCount = 0⌝) ** reloadSkipRest) ** baseFrame) h
    cpsNBranchWithin
      expTwoMulFixedReloadIterStepBound
      (base + 44)
      (expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11)
      [((base + 44), (fun h => skipLoopPost h ∨ reloadLoopPost h)),
       ((base + 296), (fun h => skipExitPost h ∨ reloadExitPost h))] := by
  intro bit c6New squareW rw baseFrame ptrFrame skipCondFrame skipRest skipCondRest
    reloadCondFrame reloadSkipRest reloadCondRest skipLoopPost skipExitPost
    reloadLoopPost reloadExitPost
  exact cpsBranchWithin_as_cpsNBranchWithin
    (exp_msb_bit_test_fixed_full_iter_merged_exit_branch_expIterBodyFullMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase)

end EvmAsm.Evm64.Exp.Compose
