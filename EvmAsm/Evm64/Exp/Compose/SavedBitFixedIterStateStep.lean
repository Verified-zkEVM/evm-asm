/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStateStep

  State-count-aware wrappers for one fixed EXP iteration.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepBounds

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
def expTwoMulFixedStateStepBranchPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (controlC6 e iterCount ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 : Word)
    (bit : Bool)
    (v7 v10 v11 d0 d1 d2 d3 : Word)
    (base : Word) (frame : Assertion) : Assertion :=
  let outW := expTwoMulFixedBranchResult bit
    a0 a1 a2 a3 r0 r1 r2 r3
  expTwoMulFixedIterPreNWithStateFrame (k + 1) baseWord exponentWord
    (controlC6 + signExtend12 (-1 : BitVec 12))
    (e <<< (1 : BitVec 6).toNat)
    (controlC6 + signExtend12 (-1 : BitVec 12))
    (expTwoMulIterCountNew iterCount)
    v10
    ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
    ptr nextLimb sp evmSp
    (outW.getLimbN 3)
    (expTwoMulFixedBranchReturnPc bit base)
    (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
    (outW.getLimbN 3)
    d0 d1 d2 d3
    (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
    (outW.getLimbN 3)
    a0 a1 a2 a3 v7 v11 frame

/-- Reload-pointer residual with the successor iteration state bundled as a
    single pure state assertion.  This is the reload-side analogue of
    `expTwoMulFixedIterPreNWithStateFrame` for the fixed-loop induction. -/
@[irreducible]
def expTwoMulFixedReloadBranchResidualWithStateFrame
    (bit : Bool) (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) : Assertion :=
  if bit then
    let outW := expTwoMulFixedBranchResult true
      a0 a1 a2 a3 r0 r1 r2 r3
    ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
      expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
        e c6 ptr nextLimb base) **
      expTwoMulFixedIterStateAssertion baseWord exponentWord (k + 1)
        (expTwoMulIterCountNew iterCount) nextLimb 64
        (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
        (outW.getLimbN 0) (outW.getLimbN 1)
        (outW.getLimbN 2) (outW.getLimbN 3) **
      frame)
  else
    let outW := expTwoMulFixedBranchResult false
      a0 a1 a2 a3 r0 r1 r2 r3
    ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
      r0 r1 r2 r3
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
      expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
        e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
      expTwoMulFixedIterStateAssertion baseWord exponentWord (k + 1)
        (expTwoMulIterCountNew iterCount) nextLimb 64
        (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
        (outW.getLimbN 0) (outW.getLimbN 1)
        (outW.getLimbN 2) (outW.getLimbN 3) **
      frame)

theorem expTwoMulFixedReloadBranchResidualWithStateFrame_false
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} :
    expTwoMulFixedReloadBranchResidualWithStateFrame false k
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base v6 v7 v10 v11 d0 d1 d2 d3
      frame =
      (let squareW := expSquaringCallSquareW r0 r1 r2 r3
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        expTwoMulFixedIterStateAssertion baseWord exponentWord (k + 1)
          (expTwoMulIterCountNew iterCount) nextLimb 64
          (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
          (squareW.getLimbN 0) (squareW.getLimbN 1)
          (squareW.getLimbN 2) (squareW.getLimbN 3) **
        frame)) := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame]
  rfl

theorem expTwoMulFixedReloadBranchResidualWithStateFrame_true
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} :
    expTwoMulFixedReloadBranchResidualWithStateFrame true k
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base v6 v7 v10 v11 d0 d1 d2 d3
      frame =
      (let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        expTwoMulFixedIterStateAssertion baseWord exponentWord (k + 1)
          (expTwoMulIterCountNew iterCount) nextLimb 64
          (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
          (rw.getLimbN 0) (rw.getLimbN 1)
          (rw.getLimbN 2) (rw.getLimbN 3) **
        frame)) := by
  rw [expTwoMulFixedReloadBranchResidualWithStateFrame]
  rfl

theorem expTwoMulFixedReloadBranchResidualWithStateFrame_pcFree
    {bit : Bool} {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} [Assertion.PCFree frame] :
    (expTwoMulFixedReloadBranchResidualWithStateFrame bit k
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
      sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 frame).pcFree := by
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false]
    dsimp
    pcFree
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true]
    dsimp
    pcFree

instance pcFreeInst_expTwoMulFixedReloadBranchResidualWithStateFrame
    (bit : Bool) (baseWord exponentWord : EvmWord) (k : Nat)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) [Assertion.PCFree frame] :
    Assertion.PCFree
      (expTwoMulFixedReloadBranchResidualWithStateFrame bit k
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame) :=
  ⟨expTwoMulFixedReloadBranchResidualWithStateFrame_pcFree⟩

/-- Pure successor-state payload carried by a state-framed reload residual. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_pure
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    let outW := expTwoMulFixedBranchResult bit
      a0 a1 a2 a3 r0 r1 r2 r3
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      (outW.getLimbN 0) (outW.getLimbN 1)
      (outW.getLimbN 2) (outW.getLimbN 3) := by
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false] at h
    obtain ⟨psHead, _psFrame, _hDisjointFrame, _hUnionFrame,
      _hHead, hStateFrame⟩ := h
    obtain ⟨_psState, _psFrameTail, _hDisjointStateFrame,
      _hUnionStateFrame, hState, _hFrameTail⟩ := hStateFrame
    rw [expTwoMulFixedIterStateAssertion_unfold] at hState
    simpa [expTwoMulFixedBranchResult_false] using hState.2
  · rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true] at h
    obtain ⟨psHead, _psFrame, _hDisjointFrame, _hUnionFrame,
      _hHead, hStateFrame⟩ := h
    obtain ⟨_psState, _psFrameTail, _hDisjointStateFrame,
      _hUnionStateFrame, hState, _hFrameTail⟩ := hStateFrame
    rw [expTwoMulFixedIterStateAssertion_unfold] at hState
    simpa [expTwoMulFixedBranchResult_true] using hState.2

/-- Named false-bit specialization of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_pure`. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_false_pure
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
  simpa [expTwoMulFixedBranchResult_false] using
    expTwoMulFixedReloadBranchResidualWithStateFrame_pure
      (bit := false) h

/-- Named true-bit specialization of
    `expTwoMulFixedReloadBranchResidualWithStateFrame_pure`. -/
theorem expTwoMulFixedReloadBranchResidualWithStateFrame_true_pure
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedReloadBranchResidualWithStateFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3).getLimbN 3) := by
  simpa [expTwoMulFixedBranchResult_true] using
    expTwoMulFixedReloadBranchResidualWithStateFrame_pure
      (bit := true) h

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_state_pure
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (hCount :
      expTwoMulFixedIterCountInvariant (k + 1)
        (expTwoMulIterCountNew iterCount))
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    let outW := expTwoMulFixedBranchResult bit
      a0 a1 a2 a3 r0 r1 r2 r3
    expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
      (expTwoMulIterCountNew iterCount) nextLimb 64
      (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
      (outW.getLimbN 0) (outW.getLimbN 1)
      (outW.getLimbN 2) (outW.getLimbN 3) := by
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at h
    obtain ⟨psControl, _psFrame, _hDisjointControl, _hUnionControl,
      hControlFrame, _hFrame⟩ := h
    obtain ⟨psCursor, _psControl, _hDisjointCursor, _hUnionCursor,
      hCursorFrame, hControl⟩ := hControlFrame
    obtain ⟨psSemantic, _psCursor, _hDisjointSemantic, _hUnionSemantic,
      hSemanticFrame, hCursor⟩ := hCursorFrame
    obtain ⟨_psScratch, _psSemantic, _hDisjointScratch, _hUnionScratch,
      _hScratch, hSemantic⟩ := hSemanticFrame
    rw [expTwoMulFixedSemanticInvariant_unfold] at hSemantic
    rw [expTwoMulFixedCursorAssertion_unfold] at hCursor
    rw [expTwoMulFixedControlAssertion_unfold] at hControl
    exact ⟨hSemantic.2, hCursor.2, hControl.2, hCount⟩
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at h
    obtain ⟨psControl, _psFrame, _hDisjointControl, _hUnionControl,
      hControlFrame, _hFrame⟩ := h
    obtain ⟨psCursor, _psControl, _hDisjointCursor, _hUnionCursor,
      hCursorFrame, hControl⟩ := hControlFrame
    obtain ⟨psSemantic, _psCursor, _hDisjointSemantic, _hUnionSemantic,
      hSemanticFrame, hCursor⟩ := hCursorFrame
    obtain ⟨_psScratch, _psSemantic, _hDisjointScratch, _hUnionScratch,
      _hScratch, hSemantic⟩ := hSemanticFrame
    rw [expTwoMulFixedSemanticInvariant_unfold] at hSemantic
    rw [expTwoMulFixedCursorAssertion_unfold] at hCursor
    rw [expTwoMulFixedControlAssertion_unfold] at hControl
    exact ⟨hSemantic.2, hCursor.2, hControl.2, hCount⟩

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_to_stateFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (hCount :
      expTwoMulFixedIterCountInvariant (k + 1)
        (expTwoMulIterCountNew iterCount))
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
      sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 frame ps := by
  have hState :=
    expTwoMulFixedReloadBranchResidualWithControlFrame_state_pure
      (bit := bit) hCount h
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at h
    have hStateFalse :
        expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
          (expTwoMulIterCountNew iterCount) nextLimb 64
          (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
          ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3) := by
      simpa [expTwoMulFixedBranchResult_false] using hState
    simp only [expTwoMulFixedSemanticInvariant_unfold,
      expTwoMulFixedCursorAssertion_unfold,
      expTwoMulFixedControlAssertion_unfold] at h
    rw [expTwoMulFixedReloadBranchResidualWithStateFrame_false]
    simp only [expTwoMulFixedIterStateAssertion_unfold]
    rw [pure_assertion_eq_emp_of_true hStateFalse]
    rw [pure_assertion_eq_emp_of_true hStateFalse.1,
      pure_assertion_eq_emp_of_true hStateFalse.2.1,
      pure_assertion_eq_emp_of_true hStateFalse.2.2.1] at h
    simpa [sepConj_emp_right', sepConj_emp_left'] using h
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at h
    have hStateTrue :
        expTwoMulFixedIterStateInvariant baseWord exponentWord (k + 1)
          (expTwoMulIterCountNew iterCount) nextLimb 64
          (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3).getLimbN 0)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3).getLimbN 1)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3).getLimbN 2)
          ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3).getLimbN 3) := by
      simpa [expTwoMulFixedBranchResult_true] using hState
    simp only [expTwoMulFixedSemanticInvariant_unfold,
      expTwoMulFixedCursorAssertion_unfold,
      expTwoMulFixedControlAssertion_unfold] at h
    rw [expTwoMulFixedReloadBranchResidualWithStateFrame_true]
    simp only [expTwoMulFixedIterStateAssertion_unfold]
    rw [pure_assertion_eq_emp_of_true hStateTrue]
    rw [pure_assertion_eq_emp_of_true hStateTrue.1,
      pure_assertion_eq_emp_of_true hStateTrue.2.1,
      pure_assertion_eq_emp_of_true hStateTrue.2.2.1] at h
    simpa [sepConj_emp_right', sepConj_emp_left'] using h

/-- Repackage the branch side of a fixed-loop step post from the older
    `WithControlFrame` surface to the state-carrying `WithStateFrame` surface.
    Reload-pointer branches remain as residuals because they still need their
    reload block before re-entering the next iteration precondition. -/
theorem expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (h :
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps) :
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedStateStepBranchPre k baseWord exponentWord
        controlC6 e iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 bit
        v7 v10 v11 d0 d1 d2 d3 base frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  rcases expTwoMulFixedIterStepPostNWithControlFrame_cases h with
    hBranch | hReload
  · rcases hBranch with ⟨bit, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    exact Or.inl
      ⟨bit, v7, v10, v11, d0, d1, d2, d3,
        by
          simpa only [expTwoMulFixedStateStepBranchPre,
            expTwoMulFixedStepPostBranchPre] using
            expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
              (expTwoMulFixedIterCountInvariant_succ hk hCount) hPre⟩
  · exact Or.inr hReload

/-- State-shaped version of
    `expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload`: both
    the ordinary branch and reload branch expose the successor iteration state
    needed by the Nat-induction path. -/
theorem expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reloadState
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (h :
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps) :
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedStateStepBranchPre k baseWord exponentWord
        controlC6 e iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 bit
        v7 v10 v11 d0 d1 d2 d3 base frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  rcases
    expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload
      hk hCount h with hBranch | hReload
  · exact Or.inl hBranch
  · rcases hReload with ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hReload⟩
    exact Or.inr
      ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3,
        expTwoMulFixedReloadBranchResidualWithControlFrame_to_stateFrame
          (bit := bit) (expTwoMulFixedIterCountInvariant_succ hk hCount)
          hReload⟩

/-- Case-loop post bridge for the fixed-loop induction: from the current
    semantic state, the loop-back post either re-enters the next state-carrying
    iteration precondition, or lands in the reload-pointer residual branch. -/
theorem expTwoMulFixedIterCaseLoopPost_branchState_or_reload
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedStateStepBranchPre k baseWord exponentWord
        controlC6 e iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 bit
        v7 v10 v11 d0 d1 d2 d3 base frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  exact
    expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reload
      hk hState.2.2.2
      (expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1 h)

/-- Case-loop bridge with the reload residual also repackaged around the
    successor state assertion. -/
theorem expTwoMulFixedIterCaseLoopPost_branchState_or_reloadState
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedStateStepBranchPre k baseWord exponentWord
        controlC6 e iterCount ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 bit
        v7 v10 v11 d0 d1 d2 d3 base frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
        baseWord exponentWord iterCount e controlC6 ptr nextLimb
        nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  exact
    expTwoMulFixedIterStepPostNWithControlFrame_branchState_or_reloadState
      hk hState.2.2.2
      (expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1 h)

/-- CPS eliminator for a fixed step post whose ordinary branch continuations
    are already stated over the state-carrying next-iteration precondition. -/
theorem cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_branchState_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7 v10 v11 d0 d1 d2 d3 base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
    (fun bit v7 v10 v11 d0 d1 d2 d3 =>
      cpsTripleWithin_weaken
        (fun _ h =>
          expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
            (expTwoMulFixedIterCountInvariant_succ hk hCount)
            (by
              simpa only [expTwoMulFixedStepPostBranchPre] using h))
        (fun _ h => h)
        (by
          simpa only [expTwoMulFixedStateStepBranchPre] using
            hBranch bit v7 v10 v11 d0 d1 d2 d3))
    hReload

/-- CPS eliminator whose ordinary and reload continuations are both stated
    over successor-state surfaces. -/
theorem cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_state_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7 v10 v11 d0 d1 d2 d3 base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_branchState_elim
    hk hCount hBranch
    (fun bit v6 v7 v10 v11 d0 d1 d2 d3 =>
      cpsTripleWithin_weaken
        (fun _ h =>
          expTwoMulFixedReloadBranchResidualWithControlFrame_to_stateFrame
            (bit := bit) (expTwoMulFixedIterCountInvariant_succ hk hCount) h)
        (fun _ h => h)
        (hReload bit v6 v7 v10 v11 d0 d1 d2 d3))

/-- CPS case-loop bridge for the fixed-loop induction.  The non-reload
    recursive edge is presented as a `WithStateFrame (k+1)` precondition;
    reload-pointer edges stay as residuals for the existing reload handlers. -/
theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_branchState_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7 v10 v11 d0 d1 d2 d3 base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      Q := by
  simpa [Nat.zero_add, CodeReq.union_empty_left] using
    cpsTripleWithin_seq
      (CodeReq.Disjoint.empty_left cr)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        addr frame hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1)
      (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_branchState_elim
        hk hState.2.2.2
        hBranch
        hReload)

/-- CPS case-loop bridge with both recursive edge shapes carrying the
    successor iteration state. -/
theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_state_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e controlC6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hState :
      expTwoMulFixedIterStateInvariant baseWord exponentWord k
        iterCount e controlC6 ptr nextLimb evmSp r0 r1 r2 r3)
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7 v10 v11 d0 d1 d2 d3 base frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterCaseLoopPost iterCount e controlC6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      Q := by
  simpa [Nat.zero_add, CodeReq.union_empty_left] using
    cpsTripleWithin_seq
      (CodeReq.Disjoint.empty_left cr)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        addr frame hk hBase hState.2.1 hState.2.2.1 hNextNext hState.1)
      (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_state_elim
        hk hState.2.2.2
        hBranch
        hReload)

/-- Bounded one-step wrapper whose nonzero decremented-count premise comes
    from the bundled fixed-loop count invariant. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
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
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
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
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

/-- One bounded fixed-loop step followed by successor-state continuations.
    This is the induction-facing wrapper: callers provide continuations for
    the no-reload recursive precondition and reload residual, both carrying
    the successor state. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound nSteps : Nat} {exit : Word} {cr : CodeReq}
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
    (hBound : 193 ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
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
    cpsTripleWithin (nBound + nSteps) (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q :=
  cpsTripleWithin_seq
    hDisjoint
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame hFrame hbase hControlMachine
      hk hCount hBase hNextNext hBound)
    (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_state_elim
      (by omega) hCount
      hBranch
      hReload)

/-- Variant of `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step`
    whose precondition carries a semantic control counter separated from the
    machine `x6` scratch register.  The current adapter covers the call sites
    where the semantic and machine counters still agree, while exposing the
    `WithControlFrame` surface used by the generic induction path. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithControlFrame_state_step_of_control_eq_machine
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound nSteps : Nat} {exit : Word} {cr : CodeReq}
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
    (hBound : 193 ≤ nBound)
    (hBranch :
      ∀ (bit : Bool)
        (v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
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
    cpsTripleWithin (nBound + nSteps) (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
      (expTwoMulFixedIterPreNWithControlFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame)
      Q := by
  intro R hR s hcr hPreR hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, hPre, hRps⟩ := hPreR
  have hStatePre :
      expTwoMulFixedIterPreNWithStateFrame k baseWord exponentWord
        controlC6 e machineC6 iterCount v10 v18 ptr nextLimb sp evmSp
        tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
        a0 a1 a2 a3 v7 v11 frame psPre :=
    expTwoMulFixedIterPreNWithControlFrame_to_iterPreNWithStateFrame
      hCount hPre
  exact
    cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base frame Q hDisjoint hFrame hbase
      hControlMachine hk hCount hBase hNextNext hBound hBranch hReload
      R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, hStatePre, hRps⟩
      hpc

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_state_step
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound nSteps : Nat} {exit : Word} {cr : CodeReq}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (Q : Assertion)
    (hDisjoint :
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).Disjoint cr)
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
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedStateStepBranchPre k baseWord exponentWord
            controlC6 e iterCount ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 bit
            v7' v10' v11' d0' d1' d2' d3' base empAssertion)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit cr
          (expTwoMulFixedReloadBranchResidualWithStateFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q) :
    cpsTripleWithin (nBound + nSteps) (base + 44) exit
      ((evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base).union cr)
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
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_state_step
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base empAssertion Q hDisjoint
      (by pcFree) hbase hControlMachine hk hCount hBase hNextNext hBound
      hBranch hReload)

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nBound : Nat}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
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
  cpsTripleWithin_expTwoMulFixedIterPreNWithState_to_stepPost_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound

/-- Count-aware framed eliminator wrapper for one fixed EXP iteration.

    This is the eliminator counterpart of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_to_stepPost_of_count_bounded`:
    the nonzero decremented-count premise is discharged from the bundled
    count invariant, leaving the future Nat induction to provide only the
    branch/reload continuations. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {frame Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hFrame : frame.pcFree)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
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
  cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_bounded
    controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
    sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
    a0 a1 a2 a3 v7 v11 base hFrame hbase hControlMachine
    (expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255 hk hCount)
    (by omega) hBase hNextNext hBound
    (fun bit v6' v7' v10' v11' d0' d1' d2' d3' => by
      simpa only [expTwoMulFixedStepPostBranchPre] using
        hBranch bit v6' v7' v10' v11' d0' d1' d2' d3')
    hReload

/-- Unframed variant of
    `cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded`. -/
theorem cpsTripleWithin_expTwoMulFixedIterPreNWithState_stepPost_elim_of_count_bounded
    {baseWord exponentWord : EvmWord} {k : Nat}
    {nSteps nBound : Nat} {exit : Word} {Q : Assertion}
    (controlC6 e machineC6 iterCount v10 v18 ptr nextLimb
      nextNextLimb sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3
      e0 e1 e2 e3 a0 a1 a2 a3 v7 v11 : Word)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hControlMachine : controlC6 = machineC6)
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount)
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
            v7' v10' v11' d0' d1' d2' d3' empAssertion)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6' v7' v10' v11' d0' d1' d2' d3' : Word),
        cpsTripleWithin nSteps (base + 44) exit
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e controlC6 ptr nextLimb
            nextNextLimb sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6' v7' v10' v11' d0' d1' d2' d3' empAssertion)
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
    (cpsTripleWithin_expTwoMulFixedIterPreNWithStateFrame_stepPost_elim_of_count_bounded
      controlC6 e machineC6 iterCount v10 v18 ptr nextLimb nextNextLimb
      sp evmSp tOld vOld r0 r1 r2 r3 d0 d1 d2 d3 e0 e1 e2 e3
      a0 a1 a2 a3 v7 v11 base (by pcFree) hbase hControlMachine
      hk hCount hBase hNextNext hBound hBranch hReload)

end EvmAsm.Evm64.Exp.Compose
