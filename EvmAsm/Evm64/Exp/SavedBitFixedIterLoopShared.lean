/-
  Shared declaration home for the saved-bit fixed iteration loop and its
  pre-reload bridge.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedControlFrame
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadTailFrames

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expReloadDirectBranchPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 e iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (bit : Bool)
    (v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (tail : Assertion) : Assertion :=
  let outW := expTwoMulFixedBranchResult bit
    a0 a1 a2 a3 r0 r1 r2 r3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    (controlC6 + signExtend12 (-1 : BitVec 12))
    (e <<< (1 : BitVec 6).toNat)
    (controlC6 + signExtend12 (-1 : BitVec 12))
    (expTwoMulIterCountNew iterCount)
    v10'
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    ptr nextLimb sp evmSp
    (outW.getLimbN 3)
    (expTwoMulFixedBranchReturnPc bit base)
    (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
    (outW.getLimbN 3)
    d0' d1' d2' d3'
    (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
    (outW.getLimbN 3)
    a0 a1 a2 a3 v7' v11' tail

@[irreducible]
def expReloadDirectFalsePre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (tail : Assertion) : Assertion :=
  let squareW := expSquaringCallSquareW r0 r1 r2 r3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10'
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
    (squareW.getLimbN 3) (((base + 44) + 32) + 68)
    (squareW.getLimbN 0) (squareW.getLimbN 1)
    (squareW.getLimbN 2) (squareW.getLimbN 3)
    d0' d1' d2' d3'
    (squareW.getLimbN 0) (squareW.getLimbN 1)
    (squareW.getLimbN 2) (squareW.getLimbN 3)
    a0 a1 a2 a3 v7' v11' tail

@[irreducible]
def expReloadDirectTruePre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (tail : Assertion) : Assertion :=
  let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
    a0 a1 a2 a3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    64 nextLimb (signExtend12 (64 : BitVec 12)) (expTwoMulIterCountNew iterCount) v10'
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb sp evmSp
    (rw.getLimbN 3) (((base + 44) + 140) + 68)
    (rw.getLimbN 0) (rw.getLimbN 1)
    (rw.getLimbN 2) (rw.getLimbN 3)
    d0' d1' d2' d3'
    (rw.getLimbN 0) (rw.getLimbN 1)
    (rw.getLimbN 2) (rw.getLimbN 3)
    a0 a1 a2 a3 v7' v11' tail

/-- Head step wrapper with direct reload re-entry continuations.

    This combines the `k < 255` reload-direct step with the `k = 255` final
    exit case. The current frame supplies the next pointer cell; recursive
    branch continuations keep that cell framed, while recursive reload
    continuations re-enter with the loaded pointer cell and branch pures. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectTailFrame ptr nextNextLimb frame))
          (Q ** expReloadDirectTailFrame ptr nextNextLimb frame))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
              frame))
          (Q ** expReloadDirectTailFrame ptr nextNextLimb frame))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
              frame))
          (Q ** expReloadDirectTailFrame ptr nextNextLimb frame))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expReloadDirectTailFrame ptr nextNextLimb frame))
      (Q ** expReloadDirectTailFrame ptr nextNextLimb frame) := by
  have hFrameCurrent :
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) ** frame).pcFree) := by
    pcFree
    exact hFrame
  simpa only [expReloadDirectTailFrame_unfold] using
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base
      (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12) ↦ₘ nextNextLimb) ** frame)
      Q hFrameCurrent hbase hControlMachine hk hBase hNextNext
      (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expReloadDirectBranchPre, expTwoMulFixedStateBranchPre,
          expReloadDirectTailFrame_unfold] using
          hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3')
      (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        cases bit
        · exact
            (by
              simpa only [expReloadDirectTailFrame_unfold] using
                cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
                  (by
                    simpa only [
                      expTwoMulFixedReloadResidualFalseNextPre,
                      expReloadDirectFalsePre,
                      expReloadDirectFalseFrame_unfold,
                      expReloadDirectTailFrame_unfold] using
                      hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3'))
        · exact
            (by
              simpa only [expReloadDirectTailFrame_unfold] using
                cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
                  (by
                    simpa only [
                      expTwoMulFixedReloadResidualTrueNextPre,
                      expReloadDirectTruePre,
                      expReloadDirectTrueFrame_unfold,
                      expReloadDirectTailFrame_unfold] using
                      hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3')))
      hExit

/-- Convenience form of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre`
    when the only carried frame is the next pointer cell required by reload
    re-entry. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb))
      (Q ** (((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) := by
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        simpa only [expReloadDirectTailFrame_emp,
          expReloadLimbDirectTailFrame_unfold] using h)
      (fun _ h => by
        simpa only [expReloadDirectTailFrame_emp,
          expReloadLimbDirectTailFrame_unfold] using h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base empAssertion Q (by pcFree) hbase
        hControlMachine hk hBase hNextNext
        (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              simpa only [expReloadDirectBranchPre,
                expReloadDirectTailFrame_emp] using h)
            (fun _ h => by
              simpa only [expReloadDirectTailFrame_emp] using h)
            (hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3'))
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              simpa only [expReloadDirectFalsePre,
                expReloadDirectFalseFrame_emp] using h)
            (fun _ h => by
              simpa only [expReloadDirectTailFrame_emp] using h)
            (hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3'))
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => by
              simpa only [expReloadDirectTruePre,
                expReloadDirectTrueFrame_emp] using h)
            (fun _ h => by
              simpa only [expReloadDirectTailFrame_emp] using h)
            (hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3'))
        hExit)

/-- Pointer-only direct head step with the current saved-limb cell expressed
    through the semantic iteration-indexed frame name. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        exact h)
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
        hNextNext
        (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectBranchPre,
            expReloadLimbDirectTailFrame_unfold] using
            hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectFalsePre,
            expReloadLimbDirectFalseFrame_unfold,
            expReloadLimbDirectTailFrame_unfold] using
            hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectTruePre,
            expReloadLimbDirectTrueFrame_unfold,
            expReloadLimbDirectTailFrame_unfold] using
            hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3')
        hExit)

/-- Ordinary no-reload direct head step with the saved-limb frame advanced to
    the recursive successor index. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_succ_no_reload_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hMod : k % 64 < 62)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedSavedNextLimbFrameN exponentWord (k + 1) ptr) := by
  have hStep :=
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_frameN_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hNextNext
      (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expReloadDirectBranchPre,
          expReloadLimbDirectTailFrame_unfold] using
          hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3')
      (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expReloadDirectFalsePre,
          expReloadLimbDirectFalseFrame_unfold,
          expReloadLimbDirectTailFrame_unfold] using
          hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3')
      (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expReloadDirectTruePre,
          expReloadLimbDirectTrueFrame_unfold,
          expReloadLimbDirectTailFrame_unfold] using
          hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3')
      hExit
  exact cpsTripleWithin_weaken
    (fun _ h => h)
    (fun _ h => by
      rw [← expTwoMulFixedSavedNextLimbFrameN_succ_no_reload
        (exponentWord := exponentWord) (ptr := ptr) hMod]
      exact h)
    hStep

/-- Direct head step with the current saved-limb cell expressed by the
    layout-correct reload-limb frame at a reload boundary. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hMod : k % 64 = 63)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
    expTwoMulFixedReloadLimbFrameN_eq_of_reload_nextNext hMod hNextNext
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        exact h)
      (fun _ h => by
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_pointer_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
        hNextNext
        (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectBranchPre,
            expReloadLimbDirectTailFrame_unfold] using
            hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectFalsePre,
            expReloadLimbDirectFalseFrame_unfold,
            expReloadLimbDirectTailFrame_unfold] using
            hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectTruePre,
            expReloadLimbDirectTrueFrame_unfold,
            expReloadLimbDirectTailFrame_unfold] using
            hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3')
        hExit)

/-- Control-invariant form of the reload-boundary direct head step.

    Recursive reload branches naturally have the current control invariant and
    the machine fact that decrementing `c6` reaches zero; this wrapper derives
    the modulo boundary fact used by the lower-level named-frame theorem. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_from_pre
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
    (expTwoMulFixedControlInvariant_reload_mod hControl hC6)
    hNextNext hBranch hReloadFalse hReloadTrue hExit

/-- From-pre variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre`.

    The current `WithStateFrame` precondition already carries the control
    invariant; this wrapper extracts it internally, leaving recursive reload
    callers to provide only the branch fact `hC6`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTailFrame ptr nextNextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectFalseFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadLimbDirectTrueFrame controlC6 e iterCount ptr
              nextLimb))
          (Q ** expReloadLimbDirectTailFrame ptr nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadLimbFrameN exponentWord k ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNextNext hBranch hReloadFalse hReloadTrue hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

/-- Reload-boundary direct head step over the two-cell reload-tail frame.

    This is the recursive handoff shape: the current `ptr - 8` cell is
    rewritten from the `nextNextLimb` premise, while the second tail cell is
    carried as the reload-limb frame for the successor state at `ptr - 8`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_control_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadTailFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedReloadLimbFrameN exponentWord k ptr :=
    expTwoMulFixedReloadLimbFrameN_eq_of_control_reload_nextNext
      hControl hC6 hNextNext
  have hTailEq :
      expTwoMulFixedReloadTailFrameN exponentWord k ptr =
        (expTwoMulFixedReloadLimbFrameN exponentWord k ptr **
          expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
            (ptr + signExtend12 (-8 : BitVec 12))) :=
    expTwoMulFixedReloadTailFrameN_handoff_of_control hControl hC6
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [hTailEq] at h
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (fun _ h => by
        rw [hTailEq, ← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base
        (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
          (ptr + signExtend12 (-8 : BitVec 12)))
        Q
        (by
          rw [expTwoMulFixedReloadLimbFrameN_unfold,
            expTwoMulFixedSavedNextLimbFrame_unfold]
          pcFree)
        hbase hControlMachine hk hBase hNextNext
        (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectBranchPre,
            expReloadDirectTailFrame_unfold,
            expReloadTailDirectTailFrameN_unfold] using
            hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectFalsePre,
            expReloadDirectFalseFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expReloadTailDirectFalseFrameN_unfold,
            expReloadTailDirectTailFrameN_unfold] using
            hReloadFalse hk_lt v7' v10' v11' d0' d1' d2' d3')
      (fun hk_lt v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectTruePre,
            expReloadDirectTrueFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expReloadTailDirectTrueFrameN_unfold,
            expReloadTailDirectTailFrameN_unfold] using
            hReloadTrue hk_lt v7' v10' v11' d0' d1' d2' d3')
        hExit)

/-- From-pre variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_control_from_pre`.

    This is the reload-boundary counterpart of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadLimbFrameN_of_pre`:
    the current precondition already carries the control invariant, so
    recursive callers only need to provide the reload branch fact. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : controlC6 + signExtend12 (-1 : BitVec 12) = 0)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadTailDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expReloadTailDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedReloadTailFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedReloadTailFrameN exponentWord k ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_reloadTailFrameN_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNextNext hBranch hReloadFalse hReloadTrue hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

open EvmAsm.Rv64

@[irreducible]
def expPreReloadDirectTailFrameN
    (exponentWord : EvmWord) (k : Nat) (ptr nextNextLimb : Word) :
    Assertion :=
  expReloadDirectTailFrame ptr nextNextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectTailFrameN_unfold
    {exponentWord : EvmWord} {k : Nat} {ptr nextNextLimb : Word} :
    expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb =
      (((((ptr + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb) **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))) := by
  rw [expPreReloadDirectTailFrameN, expReloadDirectTailFrame_unfold]

@[irreducible]
def expPreReloadDirectFalseFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectFalseFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expPreReloadDirectFalseFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) = 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expPreReloadDirectFalseFrameN, expReloadDirectFalseFrame_unfold]

@[irreducible]
def expPreReloadDirectTrueFrameN
    (exponentWord : EvmWord) (k : Nat)
    (controlC6 e iterCount ptr nextLimb : Word) : Assertion :=
  expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
    (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))

theorem expPreReloadDirectTrueFrameN_unfold
    {exponentWord : EvmWord} {k : Nat}
    {controlC6 e iterCount ptr nextLimb : Word} :
    expPreReloadDirectTrueFrameN exponentWord k
      controlC6 e iterCount ptr nextLimb =
      (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        ⌜expTwoMulIterCountNew iterCount ≠ 0⌝ **
        ⌜controlC6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
        ⌜(e >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12) ≠ 0⌝ **
        expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) := by
  rw [expPreReloadDirectTrueFrameN, expReloadDirectTrueFrame_unfold]

/-- Pre-reload direct head step over the two-cell lookahead frame.

    At `k % 64 = 62`, this step is still a no-reload step, but the recursive
    successor has `c6 = 1` and needs the reload-limb frame for the imminent
    reload. The pre-reload frame carries both the current saved-next cell and
    the successor reload cell. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k controlC6 ptr nextLimb
        evmSp)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedPreReloadFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  have hFrameEq :
      expTwoMulFixedSavedNextLimbFrame ptr nextNextLimb =
        expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr :=
    expTwoMulFixedSavedNextLimbFrameN_eq_of_nextNext hNextNext
  have hPreReloadEq :
      expTwoMulFixedPreReloadFrameN exponentWord k ptr =
        (expTwoMulFixedSavedNextLimbFrameN exponentWord k ptr **
          expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12))) :=
    expTwoMulFixedPreReloadFrameN_handoff_of_control hControl hC6
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [hPreReloadEq] at h
        rw [← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold] at h
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (fun _ h => by
        rw [hPreReloadEq, ← hFrameEq, expTwoMulFixedSavedNextLimbFrame_unfold]
        simpa only [expReloadDirectTailFrame_unfold] using h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base
        (expTwoMulFixedReloadLimbFrameN exponentWord (k + 1)
      (ptr + signExtend12 (-8 : BitVec 12)))
        Q
        (by
          rw [expTwoMulFixedReloadLimbFrameN_unfold,
            expTwoMulFixedSavedNextLimbFrame_unfold]
          pcFree)
        hbase hControlMachine hk hBase hNextNext
        (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectBranchPre,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hBranch hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectFalsePre,
            expReloadDirectFalseFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectFalseFrameN_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hReloadFalse hk_lt v6' v7' v10' v11' d0' d1' d2' d3')
        (fun hk_lt v6' v7' v10' v11' d0' d1' d2' d3' => by
          simpa only [expReloadDirectTruePre,
            expReloadDirectTrueFrame_unfold,
            expReloadDirectTailFrame_unfold,
            expPreReloadDirectTrueFrameN_unfold,
            expPreReloadDirectTailFrameN_unfold] using
            hReloadTrue hk_lt v6' v7' v10' v11' d0' d1' d2' d3')
        hExit)

/-- From-pre variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre`.

    The current `WithStateFrame` precondition already carries the control
    invariant; this wrapper extracts it internally so recursive callers only
    need to provide the pre-reload branch fact. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_pre
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hC6 : (controlC6 + signExtend12 (-1 : BitVec 12)).toNat = 1)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      k < 255 →
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            bit v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTailFrameN exponentWord k ptr nextNextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadFalse :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectFalseFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hReloadTrue :
      k < 255 →
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expReloadDirectTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v7' v10' v11' d0' d1' d2' d3' base
            (expPreReloadDirectTrueFrameN exponentWord k controlC6 e
              iterCount ptr nextLimb))
          (Q ** expPreReloadDirectTailFrameN exponentWord k ptr
            nextNextLimb))
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expTwoMulFixedPreReloadFrameN exponentWord k ptr))
      (Q ** expTwoMulFixedPreReloadFrameN exponentWord k ptr) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_reloadDirect_preReloadFrameN_of_control_from_pre
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base Q hbase hControlMachine hk hBase
      hState.2.2.1 hC6 hNextNext hBranch hReloadFalse hReloadTrue hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

end Exp.Compose
end EvmAsm.Evm64
