/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStep

  One physical fixed-loop iteration into the semantic step-post target.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostBridge
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepPost

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

private theorem cpsTripleWithin_expTwoMulFixedIterCaseExitPost_nonzero_vacuous
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    {nSteps : Nat} {entry exit : Word} {code : CodeReq} {Q : Assertion} :
    cpsTripleWithin nSteps entry exit code
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      Q := by
  intro R _hR s _hcr hExitR _hpc
  exfalso
  obtain ⟨hp, _hcompat, hExit⟩ := holdsFor_sepConj_elim_left hExitR
  exact
    expTwoMulFixedIterCaseExitPost_nonzero_count_false
      (iterCount := iterCount) (e := e) (c6 := c6) (ptr := ptr)
      (nextLimb := nextLimb) (sp := sp) (evmSp := evmSp)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
      (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
      (base := base) hne
      hExit

theorem cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    cpsTripleWithin 193 (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) := by
  have hBranch :=
    exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_closed_bound_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
      e c6 iterCount v10 v18 ptr nextLimb sp evmSp tOld vOld
      r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3 a0 a1 a2 a3
      v7 v11 base hbase
  have hLoop :
      cpsTripleWithin 0 (base + 44) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
    cpsTripleWithin_extend_code
      (fun _a _i h => by simp [CodeReq.empty] at h)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
        (base + 44) hk hBase hCursor hControl hNextNext hInv)
  have hExit :
      cpsTripleWithin 0 (base + 296) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
    cpsTripleWithin_expTwoMulFixedIterCaseExitPost_nonzero_vacuous hne
  have hMerged :=
    cpsNBranchWithin_merge hBranch (fun exit hmem => by
      simp [expTwoMulFixedIterCaseExits] at hmem
      rcases hmem with hmem | hmem
      · cases hmem
        exact hLoop
      · cases hmem
        exact hExit)
  simpa [Nat.add_zero] using hMerged

theorem cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControlFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3) :
    cpsTripleWithin 193 (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) := by
  have hFramed :
      cpsTripleWithin 193 (base + 44) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
          tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 **
          frame)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion **
          frame) :=
    cpsTripleWithin_frameR frame hFrame
      (cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControl
        e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 base hbase hne hk hBase hCursor hControl
        hNextNext hInv)
  exact
    cpsTripleWithin_weaken (fun _ h => h)
      (fun _ h => expTwoMulFixedIterStepPostNWithControlFrame_attach_frame h)
      hFramed

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_of_control_eq_machine
    {baseWord exponentWord : EvmWord} {k : Nat}
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
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    cpsTripleWithin 193 (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) := by
  intro R hR s hcr hPR hpc
  obtain ⟨hp, hcompat, psPre, psR, hDisjoint, hUnion, hPreN, hR_ps⟩ := hPR
  rcases expTwoMulFixedIterPreNWithControlFrame_pures hPreN with
    ⟨hInv, hCursor, hControl⟩
  have hControlMachineInv :
      expTwoMulFixedControlInvariant exponentWord k
        machineC6 ptr nextLimb evmSp := by
    simpa [hControlMachine] using hControl
  have hPreFrame :
      (expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame) psPre :=
    expTwoMulFixedIterPreNWithControlFrame_to_iterPre_frame hPreN
  have hPR' :
      ((expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb
        sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame) ** R).holdsFor s :=
    ⟨hp, hcompat, psPre, psR, hDisjoint, hUnion, hPreFrame, hR_ps⟩
  have hSpec :
      cpsTripleWithin 193 (base + 44) (base + 44)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterPre e machineC6 iterCount v10 v18 ptr nextLimb
          sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
          a0 a1 a2 a3 v7 v11 **
          frame)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e machineC6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
    cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControlFrame
      e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hne hk hBase hCursor
      hControlMachineInv hNextNext hInv
  simpa [← hControlMachine] using hSpec R hR s hcr hPR' hpc

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_of_control_eq_machine
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
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
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_of_control_eq_machine
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine hne
      hk hBase hNextNext)
    hStepPost

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_to_stepPost
    {baseWord exponentWord : EvmWord} {k : Nat}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64)) :
    cpsTripleWithin 193 (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_to_stepPost_of_control_eq_machine
      c6 e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase rfl hne hk hBase
      hNextNext)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_seq_stepPost
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_to_stepPost
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hne hk hBase
      hNextNext)
    hStepPost

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_to_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (frame : Assertion)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hBound : 193 ≤ nBound) :
    cpsTripleWithin nBound (base + 44) (base + 44)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_to_stepPost
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hne hk hBase
      hNextNext)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_seq_stepPost_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
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
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin nBound (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_mono_nSteps hBound
    (cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_seq_stepPost
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase hne hk hBase hNextNext
      hStepPost)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_elim_of_control_eq_machine
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
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
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3'
            frame)
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
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_of_control_eq_machine
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne hk
    hBase hNextNext
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_bit_elim_of_control_eq_machine
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
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
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3'
            frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e controlC6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3'
            frame)
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
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_seq_stepPost_of_control_eq_machine
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine hne hk
    hBase hNextNext
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_bit_elim
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_true,
          expTwoMulFixedBranchReturnPc_true] using
          hBranchTrue v6' v7' v10' v11' d0' d1' d2' d3')
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_false,
          expTwoMulFixedBranchReturnPc_false] using
          hBranchFalse v6' v7' v10' v11' d0' d1' d2' d3')
      hReloadTrue hReloadFalse)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
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
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3'
            frame)
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
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_elim_of_control_eq_machine
      c6 e c6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase rfl hne hk hBase hNextNext
      hBranch hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPreNWithFrame_stepPost_bit_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
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
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3'
            frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3'
            frame)
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
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPreNWithFrame k baseWord exponentWord
        e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_weaken
    (fun _ h =>
      expTwoMulFixedIterPreNWithFrame_to_iterPreNWithControlFrame h)
    (fun _ h => h)
    (cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_stepPost_bit_elim_of_control_eq_machine
      c6 e c6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hFrame hbase rfl hne hk hBase hNextNext
      hBranchTrue hBranchFalse hReloadTrue hReloadFalse)

theorem cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion)
        Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControl
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base hbase hne hk hBase hCursor hControl
    hNextNext hInv)
    hStepPost

theorem cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControlFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hStepPost :
      cpsTripleWithin nSteps (base + 44) exit
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
          iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 base frame)
        Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame)
      Q :=
  cpsTripleWithin_seq_same_cr
    (cpsTripleWithin_expTwoMulFixedIterPre_to_stepPostNWithControlFrame
      e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hne hk hBase hCursor
      hControl hNextNext hInv)
    hStepPost

theorem cpsTripleWithin_expTwoMulFixedIterPre_stepPostNWithControl_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3'
            empAssertion)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControl
    e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
    tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hbase hne hk hBase hCursor hControl
    hNextNext hInv
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPre_stepPostNWithControlFrame_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7' v10' v11' d0' d1' d2' d3'
            frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControlFrame
    e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
    tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hne hk hBase hCursor
    hControl hNextNext hInv
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
      (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre] using
          hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
      hReload)

theorem cpsTripleWithin_expTwoMulFixedIterPre_stepPostNWithControl_bit_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3'
            empAssertion)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3'
            empAssertion)
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControl
    e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
    tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hbase hne hk hBase hCursor hControl
    hNextNext hInv
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_bit_elim
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_true,
          expTwoMulFixedBranchReturnPc_true] using
          hBranchTrue v6' v7' v10' v11' d0' d1' d2' d3')
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_false,
          expTwoMulFixedBranchReturnPc_false] using
          hBranchFalse v6' v7' v10' v11' d0' d1' d2' d3')
      hReloadTrue hReloadFalse)

theorem cpsTripleWithin_expTwoMulFixedIterPre_stepPostNWithControlFrame_bit_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps : Nat} {exit : Word} {frame Q : Assertion}
    (e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
      tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hne : expTwoMulIterCountNew iterCount ≠ 0)
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (hBranchTrue :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7' v10' v11' d0' d1' d2' d3'
            frame)
          Q)
    (hBranchFalse :
      ∀ (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7' v10' v11' d0' d1' d2' d3'
            frame)
          Q)
    (hReloadTrue :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q)
    (hReloadFalse :
      ∀ (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' frame)
          Q) :
    cpsTripleWithin (193 + nSteps) (base + 44) exit
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre e c6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 **
        frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterPre_seq_stepPostNWithControlFrame
    e c6 iterCount v10 v18 ptr nextLimb nextNextLimb sp evmSp
    tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hne hk hBase hCursor
    hControl hNextNext hInv
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_bit_elim
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_true,
          expTwoMulFixedBranchReturnPc_true] using
          hBranchTrue v6' v7' v10' v11' d0' d1' d2' d3')
      (fun v6' v7' v10' v11' d0' d1' d2' d3' => by
        simpa only [expTwoMulFixedStepPostBranchPre,
          expTwoMulFixedBranchResult_false,
          expTwoMulFixedBranchReturnPc_false] using
          hBranchFalse v6' v7' v10' v11' d0' d1' d2' d3')
      hReloadTrue hReloadFalse)

end EvmAsm.Evm64.Exp.Compose
