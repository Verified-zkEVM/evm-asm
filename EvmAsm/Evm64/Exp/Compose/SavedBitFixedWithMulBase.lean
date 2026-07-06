/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMulBase

  First half of `EvmAsm.Evm64.Exp.Compose.SavedBitFixedWithMul`, split out to
  keep each file under the file-size guardrail (`scripts/check-file-size.sh`).
  `SavedBitFixedWithMul` imports this module and re-exports it transitively, so
  importers are unaffected.

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


end EvmAsm.Evm64.Exp.Compose
