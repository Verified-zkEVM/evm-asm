/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateResidualBridge

  Re-entry bridges from state-framed reload residuals to the next fixed
  iteration precondition when the caller frame supplies the next pointer cell.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateResidualPures
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Weaken the per-iteration scratch frame's `x6` value slot to ownership.
    After the counter moved to `x20`, the next `IterPre` keeps `x6` only as
    `regOwn` scratch, so the reload residual's concrete `x6` value is dropped. -/
private theorem expTwoMulFixedIterScratchIs_x6_to_regOwn_resid
    {evmSp v6 v7 v10 v11 d0 d1 d2 d3 : Word} :
    ∀ ps, expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 ps →
      (regOwn .x6 ** (.x7 ↦ᵣ v7) ** (.x10 ↦ᵣ v10) ** (.x11 ↦ᵣ v11) **
       (evmSp ↦ₘ d0) ** ((evmSp + 8) ↦ₘ d1) ** ((evmSp + 16) ↦ₘ d2) **
       ((evmSp + 24) ↦ₘ d3)) ps := by
  intro ps h
  unfold expTwoMulFixedIterScratchIs at h
  exact sepConj_mono_left (regIs_implies_regOwn .x6) _ h

@[irreducible]
def expTwoMulFixedReloadResidualFalseNextPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
    (squareW.getLimbN 3) (((base + 44) + 32) + 68)
    (squareW.getLimbN 0) (squareW.getLimbN 1)
    (squareW.getLimbN 2) (squareW.getLimbN 3)
    d0 d1 d2 d3
    (squareW.getLimbN 0) (squareW.getLimbN 1)
    (squareW.getLimbN 2) (squareW.getLimbN 3)
    a0 a1 a2 a3 v7 v11
    (expReloadDirectFalseFrame c6 e iterCount ptr nextLimb frame)

@[irreducible]
def expTwoMulFixedReloadResidualTrueNextPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) : Assertion :=
  let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
    a0 a1 a2 a3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
    (rw.getLimbN 3) (((base + 44) + 140) + 68)
    (rw.getLimbN 0) (rw.getLimbN 1)
    (rw.getLimbN 2) (rw.getLimbN 3)
    d0 d1 d2 d3
    (rw.getLimbN 0) (rw.getLimbN 1)
    (rw.getLimbN 2) (rw.getLimbN 3)
    a0 a1 a2 a3 v7 v11
    (expReloadDirectTrueFrame c6 e iterCount ptr nextLimb frame)

/-- A false-bit reload residual can re-enter the next state-carrying fixed
    iteration precondition once the remaining frame supplies the following
    pointer cell. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (expReloadDirectTailFrame ptr nextNextLimb frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
      64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      (squareW.getLimbN 3) (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      (expReloadDirectFalseFrame c6 e iterCount ptr nextLimb frame) ps := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false] at h
  dsimp
  rw [expReloadDirectTailFrame_unfold] at h
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn_resid)) _ h
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterPre_unfold,
    expTwoMulFixedIterPointerFrame_unfold,
    expReloadDirectFalseFrame_unfold]
  simp only [expTwoMulFixedIterSkipCountPostScratchPrefix,
    expTwoMulFixedIterSkipRestScratchPrefix,
    expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold,
    expTwoMulFixedIterBaseFrame,
    expTwoMulIterBaseFrame_unfold,
    signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    ne_eq,
    evmWordIs] at h ⊢
  sep_perm h

/-- CPS form of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame`. -/
theorem cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
    {nSteps : Nat} {entry exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame Q : Assertion}
    (hNext :
      cpsTripleWithin nSteps entry exit cr
        (expTwoMulFixedReloadResidualFalseNextPre k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base
          v7 v10 v11 d0 d1 d2 d3 frame)
        Q) :
    cpsTripleWithin nSteps entry exit cr
      (expTwoMulFixedReloadBranchResidualWithStateFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (expReloadDirectTailFrame ptr nextNextLimb frame))
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      by
        simpa only [expTwoMulFixedReloadResidualFalseNextPre] using
          expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
            h)
    (fun _ h => h)
    hNext

/-- A true-bit reload residual can re-enter the next state-carrying fixed
    iteration precondition once the remaining frame supplies the following
    pointer cell. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (expReloadDirectTailFrame ptr nextNextLimb frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
      64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
      (rw.getLimbN 3) (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1)
      (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1)
      (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      (expReloadDirectTrueFrame c6 e iterCount ptr nextLimb frame) ps := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true] at h
  dsimp
  rw [expReloadDirectTailFrame_unfold] at h
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn_resid)) _ h
  rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
    expTwoMulFixedIterPreNWithState_unfold,
    expTwoMulFixedIterPre_unfold,
    expTwoMulFixedIterPointerFrame_unfold,
    expReloadDirectTrueFrame_unfold]
  simp only [expTwoMulFixedIterSkipCondCountPostScratchPrefix,
    expTwoMulFixedIterSkipCondRestScratchPrefix,
    expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame,
    expTwoMulFixedIterSkipCondRestScratchSuffix,
    expTwoMulFixedIterReloadPointerFrame_unfold,
    expTwoMulIterBaseFrame_unfold,
    signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24,
    signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56,
    ne_eq,
    evmWordIs] at h ⊢
  sep_perm h

/-- CPS form of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame`. -/
theorem cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
    {nSteps : Nat} {entry exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame Q : Assertion}
    (hNext :
      cpsTripleWithin nSteps entry exit cr
        (expTwoMulFixedReloadResidualTrueNextPre k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base
          v7 v10 v11 d0 d1 d2 d3 frame)
        Q) :
    cpsTripleWithin nSteps entry exit cr
      (expTwoMulFixedReloadBranchResidualWithStateFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3
        (expReloadDirectTailFrame ptr nextNextLimb frame))
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      by
        simpa only [expTwoMulFixedReloadResidualTrueNextPre] using
          expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
            h)
    (fun _ h => h)
    hNext

end EvmAsm.Evm64.Exp.Compose
