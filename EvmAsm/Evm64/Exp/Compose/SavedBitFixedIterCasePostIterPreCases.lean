/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostIterPreCases

  Case splits that convert fixed x19 non-reload branches to iterPre while
  leaving reload-pointer branches explicit.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterReloadPointerPures

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

theorem expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseLoopPost_scratch_cases_reloadPointerFrame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨(c6 + signExtend12 (-1 : BitVec 12)), v7, v10, v11, d0, d1, d2, d3,
        expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨(c6 + signExtend12 (-1 : BitVec 12)), v7, v10, v11, d0, d1, d2, d3,
          expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · exact Or.inr (Or.inr (Or.inl hReloadCond))
      · exact Or.inr (Or.inr (Or.inr hReloadSkip))

theorem expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps ∧
      expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps ∧
      expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  rcases expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame h with
    hSkipCond | hRest
  · exact Or.inl hSkipCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl hSkip)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        have h_pures :=
          expTwoMulFixedIterReloadCondPointerScratchFrame_pures hScratch
        rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hScratch, h_exit, h_c6, h_bit⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        have h_pures :=
          expTwoMulFixedIterReloadSkipPointerScratchFrame_pures hScratch
        rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hScratch, h_exit, h_c6, h_bit⟩))

theorem expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame_pures_unframed
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) ps ∧
      expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount ≠ 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps ∧
      expTwoMulIterCountNew iterCount ≠ 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  have hFrame :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** empAssertion) ps := by
    simpa [sepConj_emp_right'] using h
  simpa [sepConj_emp_right'] using
    (expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame_pures
      (frame := empAssertion) hFrame)

theorem expTwoMulFixedIterCaseExitPost_iterPre_or_reloadPointerFrame
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) := by
  rcases expTwoMulFixedIterCaseExitPost_scratch_cases_reloadPointerFrame h with
    hSkipCond | hRest
  · rcases hSkipCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
    exact Or.inl
      ⟨(c6 + signExtend12 (-1 : BitVec 12)), v7, v10, v11, d0, d1, d2, d3,
        expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨(c6 + signExtend12 (-1 : BitVec 12)), v7, v10, v11, d0, d1, d2, d3,
          expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · exact Or.inr (Or.inr (Or.inl hReloadCond))
      · exact Or.inr (Or.inr (Or.inr hReloadSkip))

theorem expTwoMulFixedIterCaseExitPost_iterPre_or_reloadPointerFrame_pures
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) **
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps ∧
      expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps ∧
      expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  rcases expTwoMulFixedIterCaseExitPost_iterPre_or_reloadPointerFrame h with
    hSkipCond | hRest
  · exact Or.inl hSkipCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl hSkip)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        have h_pures :=
          expTwoMulFixedIterReloadCondPointerScratchFrame_pures hScratch
        rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hScratch, h_exit, h_c6, h_bit⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        have h_pures :=
          expTwoMulFixedIterReloadSkipPointerScratchFrame_pures hScratch
        rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hScratch, h_exit, h_c6, h_bit⟩))

theorem expTwoMulFixedIterCaseExitPost_iterPre_or_reloadPointerFrame_pures_unframed
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (h :
      expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      let rw := expTwoMulCondRw squareW a0 a1 a2 a3
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        a0 a1 a2 a3 v7 v11) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) ps ∧
      expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3
        (expTwoMulIterCountNew iterCount = 0) **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) ps ∧
      expTwoMulIterCountNew iterCount = 0 ∧
      c6 + signExtend12 (-1 : BitVec 12) = 0 ∧
      (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0) := by
  have hFrame :
      (expTwoMulFixedIterCaseExitPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base ** empAssertion) ps := by
    simpa [sepConj_emp_right'] using h
  simpa [sepConj_emp_right'] using
    (expTwoMulFixedIterCaseExitPost_iterPre_or_reloadPointerFrame_pures
      (frame := empAssertion) hFrame)

end EvmAsm.Evm64.Exp.Compose
