/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterPreNPost

  Adapters from fixed iteration post cases to the semantic/cursor/control
  carrying `expTwoMulFixedIterPreN` family.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedBoolStep
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterReloadPointerPures
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariantWithControl

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

def expTwoMulFixedBranchReturnPc (bit : Bool) (base : Word) : Word :=
  if bit then (((base + 44) + 140) + 68) else (((base + 44) + 32) + 68)

theorem expTwoMulFixedBranchReturnPc_false (base : Word) :
    expTwoMulFixedBranchReturnPc false base = (((base + 44) + 32) + 68) := by
  rfl

theorem expTwoMulFixedBranchReturnPc_true (base : Word) :
    expTwoMulFixedBranchReturnPc true base = (((base + 44) + 140) + 68) := by
  rfl

@[irreducible]
def expTwoMulFixedReloadBranchResidualWithControlFrame
    (bit : Bool) (k : Nat) (baseWord exponentWord : EvmWord)
    (iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word)
    (frame : Assertion) : Assertion :=
  if bit then
    let outW := expTwoMulFixedBranchResult true
      a0 a1 a2 a3 r0 r1 r2 r3
    (((((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
      expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
        e c6 ptr nextLimb base) **
      expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)) **
      expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
      expTwoMulFixedControlAssertion exponentWord (k + 1)
        64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
      frame)
  else
    let outW := expTwoMulFixedBranchResult false
      a0 a1 a2 a3 r0 r1 r2 r3
    (((((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
      r0 r1 r2 r3
      (expTwoMulIterCountNew iterCount ≠ 0) **
      expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
      expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
        e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
      expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
        (outW.getLimbN 0) (outW.getLimbN 1) (outW.getLimbN 2)
        (outW.getLimbN 3)) **
      expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
      expTwoMulFixedControlAssertion exponentWord (k + 1)
        64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
      frame)

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_false
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} :
    expTwoMulFixedReloadBranchResidualWithControlFrame false k
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base v6 v7 v10 v11 d0 d1 d2 d3
      frame =
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
        frame)) := by
  rw [expTwoMulFixedReloadBranchResidualWithControlFrame]
  rfl

theorem expTwoMulFixedReloadBranchResidualWithControlFrame_true
    {k : Nat} {baseWord exponentWord : EvmWord}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base
      v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} :
    expTwoMulFixedReloadBranchResidualWithControlFrame true k
      baseWord exponentWord iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base v6 v7 v10 v11 d0 d1 d2 d3
      frame =
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
        frame)) := by
  rw [expTwoMulFixedReloadBranchResidualWithControlFrame]
  rfl

theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPreN_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6Reg : v6 = c6 + signExtend12 (-1 : BitVec 12))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithFrame (k + 1) baseWord exponentWord
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
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro rw
  obtain ⟨_hExit, hC6, hBitNe⟩ :=
    expTwoMulFixedIterSkipCondScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = rw := by
    dsimp [rw]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_condRw_of_ne_zero
      hBitNe
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        v6 ptr nextLimb evmSp := by
    rw [hC6Reg]
    exact hStep.2.2
  have hPre :
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
        frame) ps := by
    rw [hC6Reg]
    simpa [rw] using
      (expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithFrame_unfold,
    expTwoMulFixedIterPreN_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipScratchFrame_to_iterPreN_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hC6Reg : v6 = c6 + signExtend12 (-1 : BitVec 12))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithFrame (k + 1) baseWord exponentWord
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
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro squareW
  obtain ⟨_hExit, hC6, hBitZero⟩ :=
    expTwoMulFixedIterSkipScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = squareW := by
    dsimp [squareW]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_squareW_of_zero
      hBitZero
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        v6 ptr nextLimb evmSp := by
    rw [hC6Reg]
    exact hStep.2.2
  have hPre :
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
        frame) ps := by
    rw [hC6Reg]
    simpa [squareW] using
      (expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithFrame_unfold,
    expTwoMulFixedIterPreN_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPreNWithControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
      (c6 + signExtend12 (-1 : BitVec 12))
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      ptr nextLimb sp evmSp
      (rw.getLimbN 3)
      (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro rw
  obtain ⟨_hExit, hC6, hBitNe⟩ :=
    expTwoMulFixedIterSkipCondScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = rw := by
    dsimp [rw]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_condRw_of_ne_zero
      hBitNe
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp :=
    hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        frame) ps := by
    simpa [rw] using
      (expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterSkipScratchFrame_to_iterPreNWithControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          expTwoMulFixedIterPointerFrame ptr nextLimb)) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
      (c6 + signExtend12 (-1 : BitVec 12))
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
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
      a0 a1 a2 a3 v7 v11
      frame ps := by
  intro squareW
  obtain ⟨_hExit, hC6, hBitZero⟩ :=
    expTwoMulFixedIterSkipScratchFrame_pures h
  have hStep :=
    expTwoMulFixedNoReloadInvariants_succ_of_decideBranchResult
      hk hBase hCursor hControl hC6 hInv
  have hBranchEq :
      expTwoMulFixedBranchResult
          (decide ((e >>> (63 : BitVec 6).toNat) +
            signExtend12 (0 : BitVec 12) ≠ 0))
          a0 a1 a2 a3 r0 r1 r2 r3 = squareW := by
    dsimp [squareW]
    exact expTwoMulFixedBranchResult_decide_highBit_eq_squareW_of_zero
      hBitZero
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3) := by
    rw [← hBranchEq]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1)
        (e <<< (1 : BitVec 6).toNat) :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        (c6 + signExtend12 (-1 : BitVec 12)) ptr nextLimb evmSp :=
    hStep.2.2
  have hPre :
      ((expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        frame) ps := by
    simpa [squareW] using
      (expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame h)
  rw [expTwoMulFixedIterPreNWithControlFrame_unfold,
    expTwoMulFixedIterPreNWithControl_unfold,
    expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm hPre

theorem expTwoMulFixedIterCaseLoopPost_iterPreNWithControl_or_reloadPointerFrame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      (expTwoMulFixedIterCaseLoopPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base **
        frame) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
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
      ⟨v7, v10, v11, d0, d1, d2, d3,
        expTwoMulFixedIterSkipCondScratchFrame_to_iterPreNWithControl_frame
          hk hBase hCursor hControl hInv hScratch⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
      exact Or.inr (Or.inl
        ⟨v7, v10, v11, d0, d1, d2, d3,
          expTwoMulFixedIterSkipScratchFrame_to_iterPreNWithControl_frame
            hk hBase hCursor hControl hInv hScratch⟩)
    · rcases hRest with hReloadCond | hReloadSkip
      · exact Or.inr (Or.inr (Or.inl hReloadCond))
      · exact Or.inr (Or.inr (Or.inr hReloadSkip))

theorem expTwoMulFixedIterReloadCondScratchFrame_withControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
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
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        frame) ps) :
    let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
      a0 a1 a2 a3
    (((((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base) **
        expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
          (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
          (rw.getLimbN 3)) **
        expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
        expTwoMulFixedControlAssertion exponentWord (k + 1)
          64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
        frame) ps := by
  intro rw
  obtain ⟨_hExit, hC6, hBitNe⟩ :=
    expTwoMulFixedIterReloadCondPointerScratchFrame_pures h
  have hStep :=
    expTwoMulFixedReloadInvariants_succ_of_condRw
      hk hBase hCursor hControl hC6 hNextNext hBitNe hInv
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3) := by
    dsimp [rw]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp :=
    hStep.2.2
  rw [expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm h

theorem expTwoMulFixedIterReloadSkipScratchFrame_withControl_frame
    {baseWord exponentWord : EvmWord} {k : Nat}
    {iterCount e c6 ptr nextLimb nextNextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (hk : k < 256)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord k e)
    (hControl :
      expTwoMulFixedControlInvariant exponentWord k c6 ptr nextLimb evmSp)
    (hNextNext :
      nextNextLimb = exponentWord.getLimbN (2 - (k + 1) / 64))
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord k
        r0 r1 r2 r3)
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    (((((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base) **
        expTwoMulFixedSemanticInvariant baseWord exponentWord (k + 1)
          (squareW.getLimbN 0) (squareW.getLimbN 1)
          (squareW.getLimbN 2) (squareW.getLimbN 3)) **
        expTwoMulFixedCursorAssertion exponentWord (k + 1) nextLimb) **
        expTwoMulFixedControlAssertion exponentWord (k + 1)
          64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp) **
        frame) ps := by
  intro squareW
  obtain ⟨_hExit, hC6, hBitZero⟩ :=
    expTwoMulFixedIterReloadSkipPointerScratchFrame_pures h
  have hStep :=
    expTwoMulFixedReloadInvariants_succ_of_squareW
      hk hCursor hControl hC6 hNextNext hBitZero hInv
  have h_acc :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord (k + 1)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3) := by
    dsimp [squareW]
    exact hStep.1
  have h_cursor :
      expTwoMulFixedCursorInvariant exponentWord (k + 1) nextLimb :=
    hStep.2.1
  have h_control :
      expTwoMulFixedControlInvariant exponentWord (k + 1)
        64 (ptr + signExtend12 (-8 : BitVec 12)) nextNextLimb evmSp :=
    hStep.2.2
  rw [expTwoMulFixedSemanticInvariant_unfold,
    expTwoMulFixedCursorAssertion_unfold,
    expTwoMulFixedControlAssertion_unfold]
  rw [pure_assertion_eq_emp_of_true h_acc,
    pure_assertion_eq_emp_of_true h_cursor,
    pure_assertion_eq_emp_of_true h_control]
  simp only [sepConj_emp_right']
  sep_perm h

theorem expTwoMulFixedIterCaseLoopPost_iterPreNWithControl_or_reloadWithControlFrame
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
    (∃ v7 v10 v11 d0 d1 d2 d3,
      let rw := expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3)
        a0 a1 a2 a3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
        (rw.getLimbN 3)
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ v7 v10 v11 d0 d1 d2 d3,
      let squareW := expSquaringCallSquareW r0 r1 r2 r3
      expTwoMulFixedIterPreNWithControlFrame (k + 1) baseWord exponentWord
        (c6 + signExtend12 (-1 : BitVec 12))
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
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
        a0 a1 a2 a3 v7 v11
        frame ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
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
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
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
        frame) ps) := by
  rcases
      expTwoMulFixedIterCaseLoopPost_iterPreNWithControl_or_reloadPointerFrame
        hk hBase hCursor hControl hInv h with
    hCond | hRest
  · exact Or.inl hCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr (Or.inl hSkip)
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            expTwoMulFixedIterReloadCondScratchFrame_withControl_frame
              hk hBase hCursor hControl hNextNext hInv hScratch⟩))
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩
        exact Or.inr (Or.inr (Or.inr
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            expTwoMulFixedIterReloadSkipScratchFrame_withControl_frame
              hk hCursor hControl hNextNext hInv hScratch⟩))

theorem expTwoMulFixedIterCaseLoopPost_branchPreNWithControl_or_reloadWithControlFrame
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
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
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
        frame) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
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
        frame) ps) := by
  rcases
      expTwoMulFixedIterCaseLoopPost_iterPreNWithControl_or_reloadWithControlFrame
        hk hBase hCursor hControl hNextNext hInv h with
    hCond | hRest
  · rcases hCond with ⟨v7, v10, v11, d0, d1, d2, d3, hPre⟩
    exact Or.inl
      ⟨true, v7, v10, v11, d0, d1, d2, d3, by
        simpa [expTwoMulFixedBranchResult_true,
          expTwoMulFixedBranchReturnPc_true] using hPre⟩
  · rcases hRest with hSkip | hRest
    · rcases hSkip with ⟨v7, v10, v11, d0, d1, d2, d3, hPre⟩
      exact Or.inl
        ⟨false, v7, v10, v11, d0, d1, d2, d3, by
          simpa [expTwoMulFixedBranchResult_false,
            expTwoMulFixedBranchReturnPc_false] using hPre⟩
    · exact Or.inr hRest

theorem expTwoMulFixedIterCaseLoopPost_branchPreNWithControl_or_branchReloadWithControlFrame
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
  rcases
      expTwoMulFixedIterCaseLoopPost_branchPreNWithControl_or_reloadWithControlFrame
        hk hBase hCursor hControl hNextNext hInv h with
    hPre | hReload
  · exact Or.inl hPre
  · rcases hReload with hReloadCond | hReloadSkip
    · rcases hReloadCond with
        ⟨v6, v7, v10, v11, d0, d1, d2, d3, hResidual⟩
      exact Or.inr
        ⟨true, v6, v7, v10, v11, d0, d1, d2, d3, by
          simpa [expTwoMulFixedReloadBranchResidualWithControlFrame_true]
            using hResidual⟩
    · rcases hReloadSkip with
        ⟨v6, v7, v10, v11, d0, d1, d2, d3, hResidual⟩
      exact Or.inr
        ⟨false, v6, v7, v10, v11, d0, d1, d2, d3, by
          simpa [expTwoMulFixedReloadBranchResidualWithControlFrame_false]
            using hResidual⟩

end EvmAsm.Evm64.Exp.Compose
