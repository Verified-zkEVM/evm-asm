/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterStepPost

  Named post target for one semantic fixed-loop induction step.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterPreNPost

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedIterStepPostNWithControlFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (frame : Assertion) : Assertion :=
  fun ps =>
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps)

theorem expTwoMulFixedIterStepPostNWithControlFrame_unfold
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame =
    (fun ps =>
      (∃ bit v7 v10 v11 d0 d1 d2 d3,
        let outW := expTwoMulFixedBranchResult bit
          a0 a1 a2 a3 r0 r1 r2 r3
        expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
          (c6 + signExtend12 (-1 : BitVec 12))
          (e <<< (1 : BitVec 6).toNat)
          (c6 + signExtend12 (-1 : BitVec 12))
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
          a0 a1 a2 a3 v7 v11
          frame ps) ∨
      (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
        expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
          baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
          v6 v7 v10 v11 d0 d1 d2 d3 frame ps)) := by
  delta expTwoMulFixedIterStepPostNWithControlFrame
  rfl

@[irreducible]
def expTwoMulFixedStepPostBranchPre
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (bit : Bool)
    (v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) : Assertion :=
  let outW := expTwoMulFixedBranchResult bit
    a0 a1 a2 a3 r0 r1 r2 r3
  expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
    (c6 + signExtend12 (-1 : BitVec 12))
    (e <<< (1 : BitVec 6).toNat)
    (c6 + signExtend12 (-1 : BitVec 12))
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

theorem expTwoMulFixedIterStepPostNWithControlFrame_pcFree
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} [Assertion.PCFree frame] :
    (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame).pcFree := by
  intro ps hps
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold] at hps
  rcases hps with hPre | hReload
  · rcases hPre with ⟨bit, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    exact
      (inferInstance :
        Assertion.PCFree
          (let outW := expTwoMulFixedBranchResult bit
            a0 a1 a2 a3 r0 r1 r2 r3
          expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
            (c6 + signExtend12 (-1 : BitVec 12))
            (e <<< (1 : BitVec 6).toNat)
            (c6 + signExtend12 (-1 : BitVec 12))
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
            a0 a1 a2 a3 v7 v11
            frame)).proof ps hPre
  · rcases hReload with ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hReload⟩
    cases bit
    · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at hReload
      have hPc :
          (let squareW := expSquaringCallSquareW r0 r1 r2 r3
          (((((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
            r0 r1 r2 r3
            (expTwoMulIterCountNew iterCount ≠ 0) **
            expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
            expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
              e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
            expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
              (squareW.getLimbN 0) (squareW.getLimbN 1)
              (squareW.getLimbN 2) (squareW.getLimbN 3)) **
            expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
            expTwoMulFixedControlAssertion exponentWord (k + 1)
              64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
            frame)).pcFree := by
        dsimp
        pcFree
      exact hPc ps hReload
    · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at hReload
      have hPc :
          (let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
            a0 a1 a2 a3
          (((((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3
            (expTwoMulIterCountNew iterCount ≠ 0) **
            expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
            expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
              e c6 ptr nextLimb base) **
            expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
              (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
              (rw.getLimbN 3)) **
            expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
            expTwoMulFixedControlAssertion exponentWord (k + 1)
              64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
            frame)).pcFree := by
        dsimp
        pcFree
      exact hPc ps hReload

instance pcFreeInst_expTwoMulFixedIterStepPostNWithControlFrame
    (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word)
    (frame : Assertion) [Assertion.PCFree frame] :
    Assertion.PCFree
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  ⟨expTwoMulFixedIterStepPostNWithControlFrame_pcFree⟩

theorem expTwoMulFixedIterStepPostNWithControlFrame_branch
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        a0 a1 a2 a3 v7 v11
        frame ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold]
  exact Or.inl ⟨bit, v7, v10, v11, d0, d1, d2, d3, h⟩

theorem expTwoMulFixedIterStepPostNWithControlFrame_reload
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold]
  exact Or.inr ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, h⟩

theorem expTwoMulFixedIterStepPostNWithControlFrame_branch_true
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedStepPostBranchPre k baseWord exponentWord
        iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base true
        v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  apply expTwoMulFixedIterStepPostNWithControlFrame_branch (bit := true)
  simpa only [expTwoMulFixedStepPostBranchPre] using h

theorem expTwoMulFixedIterStepPostNWithControlFrame_branch_false
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedStepPostBranchPre k baseWord exponentWord
        iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base false
        v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  apply expTwoMulFixedIterStepPostNWithControlFrame_branch (bit := false)
  simpa only [expTwoMulFixedStepPostBranchPre] using h

theorem expTwoMulFixedIterStepPostNWithControlFrame_reload_true
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3
      (((((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
          (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
          (rw.getLimbN 3)) **
        expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
        expTwoMulFixedControlAssertion exponentWord (k + 1)
          64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
        frame) ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  apply expTwoMulFixedIterStepPostNWithControlFrame_reload (bit := true)
  simpa [expTwoMulFixedReloadBranchResidualWithControlFrame_true] using h

theorem expTwoMulFixedIterStepPostNWithControlFrame_reload_false
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      (((((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
          (squareW.getLimbN 0) (squareW.getLimbN 1)
          (squareW.getLimbN 2) (squareW.getLimbN 3)) **
        expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
        expTwoMulFixedControlAssertion exponentWord (k + 1)
          64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
        frame) ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  apply expTwoMulFixedIterStepPostNWithControlFrame_reload (bit := false)
  simpa [expTwoMulFixedReloadBranchResidualWithControlFrame_false] using h

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (bit : Bool) {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    ((bit = true ∧
        (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
      (bit = false ∧
        (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0)) := by
  cases bit
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at h
    obtain ⟨psControl, _psFrame, _hDisjointControl, _hUnionControl,
      hControlFrame, _hFrame⟩ := h
    obtain ⟨psCursor, _psControl, _hDisjointCursor, _hUnionCursor,
      hCursorFrame, _hControl⟩ := hControlFrame
    obtain ⟨psSemantic, _psCursor, _hDisjointSemantic, _hUnionSemantic,
      hSemanticFrame, _hCursor⟩ := hCursorFrame
    obtain ⟨psScratch, _psSemantic, _hDisjointScratch, _hUnionScratch,
      hScratch, _hSemantic⟩ := hSemanticFrame
    have hScratchFrame :
        (let squareW := expSquaringCallSquareW r0 r1 r2 r3
        ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3
          (expTwoMulIterCountNew iterCount ≠ 0) **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
            e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
          empAssertion) psScratch) := by
      simpa [sepConj_emp_right'] using hScratch
    have h_pures :=
      expTwoMulFixedIterReloadSkipPointerScratchFrame_pures hScratchFrame
    rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
    exact ⟨h_exit, h_c6, Or.inr ⟨rfl, h_bit⟩⟩
  · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at h
    obtain ⟨psControl, _psFrame, _hDisjointControl, _hUnionControl,
      hControlFrame, _hFrame⟩ := h
    obtain ⟨psCursor, _psControl, _hDisjointCursor, _hUnionCursor,
      hCursorFrame, _hControl⟩ := hControlFrame
    obtain ⟨psSemantic, _psCursor, _hDisjointSemantic, _hUnionSemantic,
      hSemanticFrame, _hCursor⟩ := hCursorFrame
    obtain ⟨psScratch, _psSemantic, _hDisjointScratch, _hUnionScratch,
      hScratch, _hSemantic⟩ := hSemanticFrame
    have hScratchFrame :
        (let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
          a0 a1 a2 a3
        ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3
          (expTwoMulIterCountNew iterCount ≠ 0) **
          expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
          expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
            e c6 ptr nextLimb base) **
          empAssertion) psScratch) := by
      simpa [sepConj_emp_right'] using hScratch
    have h_pures :=
      expTwoMulFixedIterReloadCondPointerScratchFrame_pures hScratchFrame
    rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
    exact ⟨h_exit, h_c6, Or.inl ⟨rfl, h_bit⟩⟩

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_true_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  rcases
    expTwoMulFixedReloadBranchResidualWithControlFrame_pures
      (bit := true) h with
    ⟨h_exit, h_c6, h_bit_cases⟩
  rcases h_bit_cases with h_bit | h_bit
  · exact ⟨h_exit, h_c6, h_bit.2⟩
  · cases h_bit.1

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_false_pures
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    (h :
      expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) :
    expTwoMulIterCountNew iterCount ≠ 0 ∧
    c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  rcases
    expTwoMulFixedReloadBranchResidualWithControlFrame_pures
      (bit := false) h with
    ⟨h_exit, h_c6, h_bit_cases⟩
  rcases h_bit_cases with h_bit | h_bit
  · cases h_bit.1
  · exact ⟨h_exit, h_c6, h_bit.2⟩

theorem expTwoMulFixedIterStepPostNWithControlFrame_cases
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps) :
    (∃ bit v7 v10 v11 d0 d1 d2 d3,
      let outW := expTwoMulFixedBranchResult bit
        a0 a1 a2 a3 r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ bit v6 v7 v10 v11 d0 d1 d2 d3,
      expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
        baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
        sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
        v6 v7 v10 v11 d0 d1 d2 d3 frame ps) := by
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold] at h
  exact h

theorem expTwoMulFixedIterStepPostNWithControlFrame_elim
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion} {ps : PartialState}
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        (let outW := expTwoMulFixedBranchResult bit
          a0 a1 a2 a3 r0 r1 r2 r3
        expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
          (c6 + signExtend12 (-1 : BitVec 12))
          (e <<< (1 : BitVec 6).toNat)
          (c6 + signExtend12 (-1 : BitVec 12))
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
          a0 a1 a2 a3 v7 v11
          frame ps) →
        Q ps)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
          baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
          sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
          v6 v7 v10 v11 d0 d1 d2 d3 frame ps →
        Q ps)
    (h :
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps) :
    Q ps := by
  rcases expTwoMulFixedIterStepPostNWithControlFrame_cases h with
    hNext | hReloadCase
  · rcases hNext with ⟨bit, v7, v10, v11, d0, d1, d2, d3, hNext⟩
    exact hBranch bit v7 v10 v11 d0 d1 d2 d3 hNext
  · rcases hReloadCase with
      ⟨bit, v6, v7, v10, v11, d0, d1, d2, d3, hResidual⟩
    exact hReload bit v6 v7 v10 v11 d0 d1 d2 d3 hResidual

theorem expTwoMulFixedIterStepPostNWithControlFrame_attach_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion **
        frame) ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  obtain ⟨psStep, psFrame, hDisjoint, hUnion, hStep, hFrame⟩ := h
  apply expTwoMulFixedIterStepPostNWithControlFrame_elim
    (Q := fun ps' =>
      ps' = psStep →
      expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame ps)
    (fun bit v7 v10 v11 d0 d1 d2 d3 hNext _hEq => by
      apply expTwoMulFixedIterStepPostNWithControlFrame_branch (bit := bit)
      simp only [expTwoMulFixedIterPreNWithControlFrame_unfold] at hNext ⊢
      exact ⟨psStep, psFrame, hDisjoint, hUnion,
        (by simpa [sepConj_emp_right'] using hNext), hFrame⟩)
    (fun bit v6 v7 v10 v11 d0 d1 d2 d3 hResidual _hEq => by
      cases bit
      · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_false] at hResidual
        apply expTwoMulFixedIterStepPostNWithControlFrame_reload_false
        exact ⟨psStep, psFrame, hDisjoint, hUnion,
          (by simpa [sepConj_emp_right'] using hResidual), hFrame⟩
      · rw [expTwoMulFixedReloadBranchResidualWithControlFrame_true] at hResidual
        apply expTwoMulFixedIterStepPostNWithControlFrame_reload_true
        exact ⟨psStep, psFrame, hDisjoint, hUnion,
          (by simpa [sepConj_emp_right'] using hResidual), hFrame⟩)
    hStep
    rfl

theorem cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hBranch :
      ∀ (bit : Bool)
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame)
      Q := by
  intro R hR s hcr hStepR hpc
  obtain ⟨hp, hcompat, hsep⟩ := hStepR
  obtain ⟨hStep, hFrame, hdisj, hunion, hStepPost, hFramePart⟩ := hsep
  exact
    expTwoMulFixedIterStepPostNWithControlFrame_elim
      (Q := fun _ =>
        ∃ kExec, kExec ≤ nSteps ∧ ∃ s',
          stepN kExec s = some s' ∧ s'.pc = exit ∧
            (Q ** R).holdsFor s')
      (fun bit v7 v10 v11 d0 d1 d2 d3 hNext =>
        hBranch bit v7 v10 v11 d0 d1 d2 d3
          R hR s hcr
          ⟨hp, hcompat,
            ⟨hStep, hFrame, hdisj, hunion,
              (by
                simpa only [expTwoMulFixedStepPostBranchPre] using hNext),
              hFramePart⟩⟩
          hpc)
      (fun bit v6 v7 v10 v11 d0 d1 d2 d3 hResidual =>
        hReload bit v6 v7 v10 v11 d0 d1 d2 d3
          R hR s hcr
          ⟨hp, hcompat,
            ⟨hStep, hFrame, hdisj, hunion, hResidual, hFramePart⟩⟩
          hpc)
      hStepPost

theorem cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_bit_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
    (hBranchTrue :
      ∀ (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hBranchFalse :
      ∀ (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReloadTrue :
      ∀ (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReloadFalse :
      ∀ (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame)
      Q :=
  cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
    (fun bit v6 v7 v10 v11 d0 d1 d2 d3 => by
      cases bit
      · simpa only using
          hBranchFalse v6 v7 v10 v11 d0 d1 d2 d3
      · simpa only using
          hBranchTrue v6 v7 v10 v11 d0 d1 d2 d3)
    (fun bit v6 v7 v10 v11 d0 d1 d2 d3 => by
      cases bit
      · exact hReloadFalse v6 v7 v10 v11 d0 d1 d2 d3
      · exact hReloadTrue v6 v7 v10 v11 d0 d1 d2 d3)

theorem expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
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
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base frame ps := by
  rw [expTwoMulFixedIterStepPostNWithControlFrame_unfold]
  exact
    expTwoMulFixedIterCaseLoopPost_branchPreNWithControl_or_branchReloadWithControlFrame
      hk hBase hCursor hControl hNextNext hInv h

theorem expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {ps : PartialState}
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
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
      iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion ps := by
  apply
    expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
      (frame := empAssertion) hk hBase hCursor hControl hNextNext hInv
  simpa [sepConj_emp_right'] using h

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
    (addr : Word)
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
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
    cpsTripleWithin 0 addr addr CodeReq.empty
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base empAssertion) :=
  cpsTripleWithin_refl
    (fun _hp h =>
      expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControl
        hk hBase hCursor hControl hNextNext hInv h)

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
    (addr : Word)
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    (frame : Assertion)
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
    cpsTripleWithin 0 addr addr CodeReq.empty
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      (expTwoMulFixedIterStepPostNWithControlFrame k baseWord exponentWord
        iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base frame) :=
  cpsTripleWithin_refl
    (fun _hp h =>
      expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        hk hBase hCursor hControl hNextNext hInv h)

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_stepPostNWithControlFrame_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
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
        (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base bit
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReload :
      ∀ (bit : Bool)
        (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame bit (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      Q := by
  simpa [Nat.zero_add, CodeReq.union_empty_left] using
    cpsTripleWithin_seq
      (CodeReq.Disjoint.empty_left cr)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        addr frame hk hBase hCursor hControl hNextNext hInv)
      (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_elim
        hBranch hReload)

theorem cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_stepPostNWithControlFrame_bit_elim
    {nSteps : Nat} {addr exit : Word} {cr : CodeReq}
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame Q : Assertion}
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
      ∀ (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base true
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hBranchFalse :
      ∀ (v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedStepPostBranchPre k baseWord exponentWord
            iterCount e c6 ptr nextLimb sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base false
            v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReloadTrue :
      ∀ (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame true (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q)
    (hReloadFalse :
      ∀ (v6 v7 v10 v11 d0 d1 d2 d3 : Word),
        cpsTripleWithin nSteps addr exit cr
          (expTwoMulFixedReloadBranchResidualWithControlFrame false (k := k)
            baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb
            sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base
            v6 v7 v10 v11 d0 d1 d2 d3 frame)
          Q) :
    cpsTripleWithin nSteps addr exit cr
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame)
      Q := by
  simpa [Nat.zero_add, CodeReq.union_empty_left] using
    cpsTripleWithin_seq
      (CodeReq.Disjoint.empty_left cr)
      (cpsTripleWithin_expTwoMulFixedIterCaseLoopPost_to_stepPostNWithControlFrame
        addr frame hk hBase hCursor hControl hNextNext hInv)
      (cpsTripleWithin_expTwoMulFixedIterStepPostNWithControlFrame_bit_elim
        hBranchTrue hBranchFalse hReloadTrue hReloadFalse)

end EvmAsm.Evm64.Exp.Compose
