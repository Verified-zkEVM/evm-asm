/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoop

  Induction-facing wrappers for composing fixed EXP loop iterations while
  carrying the bundled semantic state.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostStateBridge
import EvmAsm.Evm64.Exp.SavedBitFixedIterStepShared
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateLoopReloadLimbFrames

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem pure_assertion_eq_emp_of_true {p : Prop} (hp : p) :
    (⌜p⌝ : Assertion) = empAssertion := by
  rw [← pure_true_eq_emp]
  funext ps
  apply propext
  constructor
  · intro h
    exact ⟨h.1, trivial⟩
  · intro h
    exact ⟨h.1, hp⟩

@[irreducible]
def expTwoMulFixedStateBranchPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 e iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (bit : Bool)
    (v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (frame : Assertion) : Assertion :=
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
    a0 a1 a2 a3 v7' v11' frame

@[irreducible]
def expTwoMulFixedStateReloadFalsePre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (_v6' v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (frame : Assertion) : Assertion :=
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
    a0 a1 a2 a3 v7' v11' frame

@[irreducible]
def expTwoMulFixedStateReloadTruePre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (e iterCount nextLimb ptr nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (_v6' v7' v10' v11' d0' d1' d2' d3' : Word)
    (base : Word) (frame : Assertion) : Assertion :=
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
    a0 a1 a2 a3 v7' v11' frame

/-- Named-bound one-step wrapper for the fixed-loop induction.

    This specializes
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step` to the
    canonical fixed reload-step bound, so a future Nat induction can recurse
    with `expTwoMulFixedReloadIterStepBound + tailBound` directly. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {cr : CodeReq}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hDisjoint :
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).Disjoint cr)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedReloadIterStepBound + nSteps)
      (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame Q hDisjoint hFrame hbase
    hControlMachine hk hCount hBase hNextNext
    (by rw [expTwoMulFixedReloadIterStepBound_eq])
    (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
      simpa only [expTwoMulFixedStateBranchPre,
        expTwoMulFixedStateStepBranchPre] using
        hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
    hReload

/-- Same-code one-step wrapper for the fixed-loop induction.

    Unlike
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step`, this
    composes the one-iteration prefix with continuations under the same
    canonical fixed EXP code. This is the form needed for recursive loop
    composition. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_sameCode
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound nSteps : Nat} {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (nBound + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
      hk hCount hBase hNextNext hBound)
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_state_elim
      (by omega) hCount
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStateBranchPre,
          expTwoMulFixedStateStepBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

/-- Fixed-bound same-code state step for the recursive loop induction. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound_sameCode
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedReloadIterStepBound + nSteps)
      (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_sameCode
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase
    hControlMachine hk hCount hBase hNextNext
    (by rw [expTwoMulFixedReloadIterStepBound_eq])
    hBranch hReload

/-- Fixed-loop one-step wrapper with the canonical remaining-body bound.

    This is the induction-step shape: if every successor state can run for
    `iterations` remaining fixed iterations, the current state can run for
    `iterations + 1` fixed iterations. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    {exit : Word} {cr : CodeReq}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hDisjoint :
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).Disjoint cr)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit cr
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps
    (expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hDisjoint hFrame hbase
      hControlMachine hk hCount hBase hNextNext hBranch hReload)

/-- Same-code fixed-loop one-step wrapper with the canonical remaining-body
    bound. This is the recursive induction-step shape over the canonical EXP
    code block. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound_sameCode
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps
    (expTwoMulFixedReloadIterStepBound_add_fixedIterationsBodyBound_le_succ
      iterations)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_fixedBound_sameCode
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase
      hControlMachine hk hCount hBase hNextNext hBranch hReload)

/-- Non-final same-code step where reload branches are supplied as direct
    continuations from the next state-carrying precondition.

    The current frame supplies the next pointer cell needed by the reload
    branch. Re-entering the recursive precondition moves that cell into the
    next iteration's pointer frame and leaves the just-loaded pointer cell plus
    branch-control pures in the recursive frame. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_reloadDirect
    {baseWord exponentWord : EvmWord} {k iterations : Nat}
    {exit : Word}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectTailFrame ptr nextNextLimb frame))
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateReloadFalsePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectFalseFrame controlC6 e iterCount ptr nextLimb
              frame))
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStateReloadTruePre k baseWord exponentWord
            e iterCount nextLimb ptr nextNextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            v6' v7' v10' v11' d0' d1' d2' d3' base
            (expReloadDirectTrueFrame controlC6 e iterCount ptr nextLimb
              frame))
          Q) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11
        (expReloadDirectTailFrame ptr nextNextLimb frame))
      Q := by
  have hFrameCurrent :
      (expReloadDirectTailFrame ptr nextNextLimb frame).pcFree := by
    rw [expReloadDirectTailFrame_unfold]
    pcFree
    exact hFrame
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound_sameCode
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base
      (expReloadDirectTailFrame ptr nextNextLimb frame)
      Q hFrameCurrent hbase hControlMachine hk hCount hBase hNextNext
      hBranch
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        cases bit
        · exact
            (by
              simpa only [expReloadDirectTailFrame_unfold] using
                cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_false_to_iterPreNWithStateFrame
                  (by
                    simpa only [
                      expTwoMulFixedReloadResidualFalseNextPre,
                      expTwoMulFixedStateReloadFalsePre,
                      expReloadDirectFalseFrame_unfold] using
                      hReloadFalse v6' v7' v10' v11' d0' d1' d2' d3'))
        · exact
            (by
              simpa only [expReloadDirectTailFrame_unfold] using
                cpsTripleWithin_expTwoMulFixedReloadBranchResidualWithStateFrame_true_to_iterPreNWithStateFrame
                  (by
                    simpa only [
                      expTwoMulFixedReloadResidualTrueNextPre,
                      expTwoMulFixedStateReloadTruePre,
                      expReloadDirectTrueFrame_unfold] using
                      hReloadTrue v6' v7' v10' v11' d0' d1' d2' d3')))

/-- Final fixed-loop state-frame wrapper.

    At semantic iteration `255`, the next decrement exits the 256-iteration
    loop. This packages the existing state-invariant final peel so the loop
    induction can use the same framed state-precondition surface as the
    recursive case. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_final_iterationsBound
    {baseWord exponentWord : EvmWord} {iterations : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 : Word)
    (base : Word)
    (frame Q : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hExit :
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame 255 baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (Q ** frame) := by
  have hStateMachine :
      expTwoMulFixedIterStateInvariant baseWord exponentWord 255
        iterCount e machineC6 ptr nextLimb evmSp r0 r1 r2 r3 := by
    simpa [hControlMachine] using hState
  have hRaw :
      cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb
          sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11)
        Q := by
    rw [expTwoMulFixedIterationsBodyBound_eq (iterations + 1)]
    exact
      exp_two_mul_fixed_iterations_body_peel_case_final_of_state_closed_bound_spec_within
        iterations
        e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
        r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
        v7 v11 base Q hbase hStateMachine hExit
  exact
    cpsTripleWithin_weaken
      (fun ps h =>
        by
          rw [expTwoMulFixedIterPreNWithStateFrame_unfold,
            expTwoMulFixedIterPreNWithState_unfold,
            expTwoMulFixedIterStateAssertion_unfold,
            pure_assertion_eq_emp_of_true hState,
            sepConj_emp_right'] at h
          exact h)
      (fun ps h => h)
      (cpsTripleWithin_frameR frame hFrame hRaw)

/-- Case-split head step for the state-carrying fixed-loop induction.

    For `k < 255` this takes the recursive same-code step; at `k = 255` it
    takes the terminal exit step. The post keeps the explicit caller frame so
    recursive callers can thread a stable framed target through the loop. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode
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
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
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
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          (Q ** frame))
    (hReload :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          (Q ** frame))
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
        a0 a1 a2 a3 v7 v11 frame)
      (Q ** frame) := by
  have hk_split : k < 255 ∨ k = 255 := by omega
  rcases hk_split with hk_lt | hk_eq
  · exact
      cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step_iterationsBound_sameCode
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base frame (Q ** frame) hFrame hbase
        hControlMachine hk_lt hState.2.2.2 hBase hNextNext
        (hBranch hk_lt)
        (hReload hk_lt)
  · subst k
    exact
      cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_final_iterationsBound
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase
        hControlMachine hState (hExit rfl)

/-- Head step wrapper that extracts the bundled state invariant from the
    `WithStateFrame` precondition itself.

    This is the form recursive callers usually need: the state invariant is
    part of the assertion surface, so the caller supplies only the arithmetic
    and semantic side conditions. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode_from_pre
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
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base frame)
          (Q ** frame))
    (hReload :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          (Q ** frame))
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
        a0 a1 a2 a3 v7 v11 frame)
      (Q ** frame) := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3 :=
    expTwoMulFixedIterPreNWithStateFrame_pure hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hFrame hbase hControlMachine
      hk hState hBase hNextNext hBranch hReload hExit
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩
      hpc

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode_from_pre`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_head_iterationsBound_sameCode_from_pre
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
          (expTwoMulFixedStateBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base empAssertion)
          Q)
    (hReload :
      k < 255 →
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin (expTwoMulFixedIterationsBodyBound iterations)
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q)
    (hExit :
      k = 255 →
      ∀ ps,
        expTwoMulFixedIterCaseExitPost iterCount e machineC6 ptr nextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base ps →
        Q ps) :
    cpsTripleWithin (expTwoMulFixedIterationsBodyBound (iterations + 1))
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q := by
  exact
    cpsTripleWithin_weaken
      (fun _ h => by
        rw [expTwoMulFixedIterPreNWithStateFrame_unfold, sepConj_emp_right']
        exact h)
      (fun _ h => by
        rw [sepConj_emp_right'] at h
        exact h)
      (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_head_iterationsBound_sameCode_from_pre
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base empAssertion Q (by pcFree) hbase
        hControlMachine hk hBase hNextNext
        (fun hk_lt bit v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => h)
            (fun _ h => by
              rw [sepConj_emp_right']
              exact h)
            (hBranch hk_lt bit v7' v10' v11' d0' d1' d2' d3'))
        (fun hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3' =>
          cpsTripleWithin_weaken
            (fun _ h => h)
            (fun _ h => by
              rw [sepConj_emp_right']
              exact h)
            (hReload hk_lt bit v6' v7' v10' v11' d0' d1' d2' d3'))
        hExit)

end EvmAsm.Evm64.Exp.Compose
