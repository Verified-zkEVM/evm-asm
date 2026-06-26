/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepBounds

  Bounded wrappers for fixed EXP iteration step eliminators.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStatePre

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_of_control_eq_machine
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine hne
      hk hBase hNextNext)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_of_control_eq_machine
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext hStepPost)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine hne
      hk hBase hNextNext hBound)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
  cpsTripleWithin_weaken
    (fun _ h => by
      rw [expTwoMulFixedIterPreNWithStateFrame_unfold, sepConj_emp_right']
      exact h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base empAssertion (by pcFree) hbase
      hControlMachine hne hk hBase hNextNext hBound)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_seq_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext hBound hStepPost)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_seq_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion)
        Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithState k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h => by
      rw [expTwoMulFixedIterPreNWithStateFrame_unfold, sepConj_emp_right']
      exact h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_seq_stepPost_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base (by pcFree) hbase hControlMachine hne
      hk hBase hNextNext hBound hStepPost)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_elim_of_control_eq_machine
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_elim_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext hBound hBranch hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_bit_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_bit_elim_of_control_eq_machine
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_true] using
          hBranchTrue v6' v7' v10' v11' d0' d1' d2' d3')
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_false] using
          hBranchFalse v6' v7' v10' v11' d0' d1' d2' d3')
      hReloadTrue hReloadFalse)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_bit_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithStateFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_bit_elim_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne
      hk hBase hNextNext hBound hBranchTrue hBranchFalse hReloadTrue
      hReloadFalse)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_elim
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hne hk hBase hNextNext
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_bit_elim_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 + nSteps ≤ nBound)
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_bit_elim
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hne hk hBase hNextNext
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_true] using
          hBranchTrue v6' v7' v10' v11' d0' d1' d2' d3')
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_false] using
          hBranchFalse v6' v7' v10' v11' d0' d1' d2' d3')
      hReloadTrue hReloadFalse)

end EvmAsm.Evm64.Exp.Compose
