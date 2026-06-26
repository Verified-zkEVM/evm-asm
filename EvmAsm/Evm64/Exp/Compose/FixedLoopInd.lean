/-
  EvmAsm.Evm64.Exp.Compose.FixedLoopInd

  Nat-indexed induction for the fixed-x19 EXP square-and-multiply loop body.

  The fixed loop body is assembled from the per-iteration direct head step
  `cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre`
  (see `SavedBitFixedInductionFrameLoopDirect`), mirroring the proven
  non-fixed template `exp_loop_from_looppost_induction_general`
  (`SavedBitLoopBodyInd`).

  This module collects the arithmetic and structural glue that the
  256-iteration assembly consumes.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedInductionFrameLoopDirect
import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedEntryExists

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- The conservative fixed-x19 256-iteration full-body bound is exactly the
    256-fold iteration-body bound.  This is the closed form consumed by the
    Nat induction over the fixed loop, which counts iterations rather than
    peeling a named first iteration. -/
theorem expTwoMulFixedFullLoopBodyBound_eq_iterationsBodyBound_256 :
    expTwoMulFixedFullLoopBodyBound = expTwoMulFixedIterationsBodyBound 256 := by
  rw [expTwoMulFixedFullLoopBodyBound_eq, expTwoMulFixedIterationsBodyBound_eq]

/-- Base case of the fixed-loop induction: the final iteration `k = 255`.

    At `k = 255` every `k < 255` head-step continuation is vacuous, so the
    direct head step
    `cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre`
    collapses to requiring only the loop-exit bridge `hExit`. -/
theorem exp_two_mul_fixed_loop_final_iteration_spec
    {baseWord exponentWord : EvmWord} {iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (255 + 1) / 64))
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithInductionFrame 255 baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (Q ** expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord 255
        controlC6 ptr nextNextLimb) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithInductionFrame_head_reloadDirect_tailOrSuccessorFrameN_of_pre
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
    nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
    e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 base Q hbase
    hControlMachine (by decide) hBase hNextNext
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide)) (fun _ => hExit)

/-- The ordinary-case continuation tail frame `expReloadLimbDirectTailFrame`
    and the induction-frame's `expTwoMulFixedSavedNextLimbFrame` are the same
    single saved-next-limb cell at `ptr - 8`.  This is the def-level bridge the
    ordinary control sub-case of the inductive step uses to reconcile the
    direct head step's continuation tail against `InductionFrameN (k+1)`. -/
theorem expReloadLimbDirectTailFrame_eq_savedNextLimbFrame
    {ptr nextNextLimb : Word} :
    expReloadLimbDirectTailFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb := by
  rw [expReloadLimbDirectTailFrame_unfold,
    expTwoMulFixedSavedNextLimbFrame_unfold]

/-- Restatement of `expReloadLimbDirectTailFrame_eq_savedNextLimbFrame` against
    the `k`-indexed saved-next-limb frame, given the standard `nextNextLimb`
    cursor equation.  Converts the ordinary continuation tail directly into the
    `InductionFrameN`-ordinary frame `expTwoMulFixedSavedNextLimbFrameN`. -/
theorem expReloadLimbDirectTailFrame_eq_savedNextLimbFrameN
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word}
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    expReloadLimbDirectTailFrame ptr nextNextLimb =
      expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr := by
  rw [expReloadLimbDirectTailFrame_eq_savedNextLimbFrame,
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext]

/-- In the ordinary control sub-case (`controlC6 - 1 ≠ 0`), the direct head
    step's reload-false continuation is vacuous: its precondition carries the
    pure fact `⌜controlC6 - 1 = 0⌝` (inside `expReloadLimbDirectFalseFrame`),
    contradicting the ordinary condition.  This discharges one of the
    `_ordinary_of_pre` continuations in the fixed-loop inductive step. -/
theorem cpsTripleWithin_expReloadDirectFalsePre_ordinary_vacuous
    {n : Nat} {entry exit_ : Word} {code : CodeReq} {Q : Assertion}
    {k : Nat} {baseWord exponentWord : EvmWord}
    {controlC6 e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 v6' v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectFalsePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v6' v7' v10' v11' d0' d1' d2' d3' base
        (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr nextLimb))
      Q := by
  intro R _ s _ hPR _
  exfalso
  delta expReloadDirectFalsePre at hPR
  simp only [] at hPR
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold] at hPR
  have hFrame :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  rw [expReloadLimbDirectFalseFrame_unfold] at hFrame
  have h2 := holdsFor_sepConj_elim_right hFrame
  have h3 := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right h2)
  exact hC6 (holdsFor_pure.mp h3)

/-- In the ordinary control sub-case (`controlC6 - 1 ≠ 0`), the direct head
    step's reload-true continuation is vacuous, by the same pure contradiction
    carried in `expReloadLimbDirectTrueFrame`. -/
theorem cpsTripleWithin_expReloadDirectTruePre_ordinary_vacuous
    {n : Nat} {entry exit_ : Word} {code : CodeReq} {Q : Assertion}
    {k : Nat} {baseWord exponentWord : EvmWord}
    {controlC6 e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 v6' v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectTruePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v6' v7' v10' v11' d0' d1' d2' d3' base
        (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr nextLimb))
      Q := by
  intro R _ s _ hPR _
  exfalso
  delta expReloadDirectTruePre at hPR
  simp only [] at hPR
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold] at hPR
  have hFrame :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  rw [expReloadLimbDirectTrueFrame_unfold] at hFrame
  have h2 := holdsFor_sepConj_elim_right hFrame
  have h3 := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right h2)
  exact hC6 (holdsFor_pure.mp h3)

end EvmAsm.Evm64.Exp.Compose
