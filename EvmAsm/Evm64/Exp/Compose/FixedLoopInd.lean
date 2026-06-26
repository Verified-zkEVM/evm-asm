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
      r0 r1 r2 r3 a0 a1 a2 a3 v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectFalsePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v7' v10' v11' d0' d1' d2' d3' base
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
      r0 r1 r2 r3 a0 a1 a2 a3 v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectTruePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v7' v10' v11' d0' d1' d2' d3' base
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

/-- Pre-reload-family analogue of
    `cpsTripleWithin_expReloadDirectFalsePre_ordinary_vacuous`: when
    `controlC6 - 1 ≠ 0` (which holds in both the ordinary and pre-reload
    control sub-cases, since pre-reload has `(controlC6-1).toNat = 1`), the
    pre-reload reload-false continuation is vacuous.  Its tail frame
    `expPreReloadDirectFalseFrameN` carries the same contradicting pure
    `⌜controlC6 - 1 = 0⌝` ahead of the extra reload-limb cell. -/
theorem cpsTripleWithin_expReloadDirectFalsePre_preReload_vacuous
    {n : Nat} {entry exit_ : Word} {code : CodeReq} {Q : Assertion}
    {k kf : Nat} {baseWord exponentWord : EvmWord}
    {controlC6 e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectFalsePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v7' v10' v11' d0' d1' d2' d3' base
        (expPreReloadDirectFalseFrameN exponentWord kf controlC6 e iterCount
          ptr nextLimb))
      Q := by
  intro R _ s _ hPR _
  exfalso
  delta expReloadDirectFalsePre at hPR
  simp only [] at hPR
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold] at hPR
  have hFrame :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  rw [expPreReloadDirectFalseFrameN_unfold] at hFrame
  have h2 := holdsFor_sepConj_elim_right hFrame
  have h3 := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right h2)
  exact hC6 (holdsFor_pure.mp h3)

/-- Pre-reload-family true-branch analogue of
    `cpsTripleWithin_expReloadDirectTruePre_ordinary_vacuous`. -/
theorem cpsTripleWithin_expReloadDirectTruePre_preReload_vacuous
    {n : Nat} {entry exit_ : Word} {code : CodeReq} {Q : Assertion}
    {k kf : Nat} {baseWord exponentWord : EvmWord}
    {controlC6 e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 v7' v10' v11' d0' d1' d2' d3' base : Word}
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) ≠ 0) :
    cpsTripleWithin n entry exit_ code
      (expReloadDirectTruePre k baseWord exponentWord e iterCount nextLimb ptr
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3
        v7' v10' v11' d0' d1' d2' d3' base
        (expPreReloadDirectTrueFrameN exponentWord kf controlC6 e iterCount
          ptr nextLimb))
      Q := by
  intro R _ s _ hPR _
  exfalso
  delta expReloadDirectTruePre at hPR
  simp only [] at hPR
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold] at hPR
  have hFrame :=
    holdsFor_sepConj_elim_right (holdsFor_sepConj_elim_left hPR)
  rw [expPreReloadDirectTrueFrameN_unfold] at hFrame
  have h2 := holdsFor_sepConj_elim_right hFrame
  have h3 := holdsFor_sepConj_elim_left (holdsFor_sepConj_elim_right h2)
  exact hC6 (holdsFor_pure.mp h3)

/-- Deep-ordinary input-frame chaining: when the *next* iteration `k+1` is
    itself ordinary (its control decrement is neither a reload nor a pre-reload)
    and the current iteration is not at a 64-bit limb boundary, the ordinary
    head step's `hBranch` continuation frame `expReloadLimbDirectTailFrame`
    coincides with the next iteration's induction-frame
    `InductionFrameN (k+1) (controlC6-1) ptr`.  This is the input-frame side of
    the deep-ordinary `hBranch` discharge in the fixed-loop induction (the
    boundary cases — pre-reload/reload of `k+1` — are handled separately). -/
theorem expReloadLimbDirectTailFrame_eq_inductionFrameN_succ_ordinary
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6' :
      (controlC6 + signExtend12 (-1 : BitVec 12)) + signExtend12 (-1 : BitVec 12)
        ≠ 0)
    (hNotPre' :
      ((controlC6 + signExtend12 (-1 : BitVec 12)) +
        signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hMod : k % 64 < 62) :
    expReloadLimbDirectTailFrame ptr nextNextLimb =
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr := by
  rw [expReloadLimbDirectTailFrame_eq_savedNextLimbFrameN hNextNext,
    expTwoMulFixedSavedNextLimbFrameN_succ_no_reload hMod,
    expTwoMulFixedInductionFrameN_ordinary_of_control hC6' hNotPre']

/-- Ordinary→pre-reload input-frame re-partition.  When the next iteration
    `k+1` is a *pre-reload* step (its control decrement has `toNat = 1`) and the
    current iteration is not at a 64-bit limb boundary, the ordinary head step's
    `hBranch` continuation tail `expReloadLimbDirectTailFrame` (one cell at
    `ptr-8`) together with the look-ahead exponent cell at `ptr-16` (supplied
    from the induction residual `R_k`) forms exactly the next iteration's
    two-cell pre-reload induction frame `InductionFrameN (k+1) (controlC6-1)`.
    This is the input-frame side of the ordinary→pre-reload `hBranch` discharge
    in the fixed-loop induction; the look-ahead cell is the one re-partitioned
    out of the residual at this boundary. -/
theorem expReloadLimbDirectTailFrame_lookahead_eq_inductionFrameN_succ_preReload
    {exponentWord : EvmWord} {k : Nat} {controlC6 ptr nextNextLimb : Word}
    (hC6' :
      ((controlC6 + signExtend12 (-1 : BitVec 12)) +
        signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hMod : k % 64 < 62) :
    (expReloadLimbDirectTailFrame ptr nextNextLimb **
      expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 2)
        (ptr + signExtend12 (-8 : BitVec 12))) =
      expTwoMulFixedInductionFrameN exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr := by
  rw [expReloadLimbDirectTailFrame_eq_savedNextLimbFrameN hNextNext,
    expTwoMulFixedSavedNextLimbFrameN_succ_no_reload hMod,
    expTwoMulFixedInductionFrameN_pre_reload_of_control hC6',
    expTwoMulFixedPreReloadFrameN_unfold]

/-- Deep-ordinary output-frame chaining (companion to
    `expReloadLimbDirectTailFrame_eq_inductionFrameN_succ_ordinary`): when the
    next iteration `k+1` is ordinary and neither `k` nor `k+1` is at a 64-bit
    limb boundary, the induction-hypothesis output frame
    `DirectHeadTailOrSuccessorFrameN (k+1) (controlC6-1) ptr` coincides with the
    ordinary head step's `hBranch` continuation tail
    `expReloadLimbDirectTailFrame ptr nextNextLimb`.  With the input-frame lemma
    this completes the deep-ordinary `hBranch` discharge: rewrite the pre, apply
    the IH, rewrite the post. -/
theorem directHeadTailOrSuccessorFrameN_succ_ordinary_eq_reloadLimbTail
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 ptr nextNextLimb nextNextLimb' : Word}
    (hC6' :
      (controlC6 + signExtend12 (-1 : BitVec 12)) + signExtend12 (-1 : BitVec 12)
        ≠ 0)
    (hNotPre' :
      ((controlC6 + signExtend12 (-1 : BitVec 12)) +
        signExtend12 (-1 : BitVec 12)).toNat ≠ 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hMod : k % 64 < 62)
    (hMod1 : (k + 1) % 64 < 62) :
    expTwoMulFixedDirectHeadTailOrSuccessorFrameN exponentWord (k + 1)
        (controlC6 + signExtend12 (-1 : BitVec 12)) ptr nextNextLimb' =
      expReloadLimbDirectTailFrame ptr nextNextLimb := by
  rw [expTwoMulFixedDirectHeadTailOrSuccessorFrameN_ordinary_of_control
    hC6' hNotPre',
    expReloadLimbDirectTailFrame_eq_savedNextLimbFrameN hNextNext,
    expTwoMulFixedSavedNextLimbFrameN_succ_no_reload hMod,
    expTwoMulFixedSavedNextLimbFrameN_succ_no_reload hMod1]

/-- Pre-reload output-frame split: the two-cell pre-reload tail frame
    `expPreReloadDirectTailFrameN` decomposes definitionally into the ordinary
    one-cell tail `expReloadLimbDirectTailFrame` (at `ptr-8`) and the look-ahead
    reload cell (at `ptr-16`).  This is the output-frame side of the
    ordinary→pre-reload discharge: after applying the IH (whose output carries
    the two-cell pre-reload frame), the look-ahead cell is returned to the
    induction residual and the ordinary continuation's required one-cell tail
    remains. -/
theorem expPreReloadDirectTailFrameN_eq_tail_lookahead
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word} :
    expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb =
      (expReloadLimbDirectTailFrame ptr nextNextLimb **
       expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
         (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expPreReloadDirectTailFrameN_unfold, expReloadLimbDirectTailFrame_unfold]

end EvmAsm.Evm64.Exp.Compose
