/-
  EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixedEntryExists

  Boundary wrappers that use the existential fixed first-iteration precondition
  produced by the fixed loop entry bridge.
-/

module

public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryEntryFixedIterPre
public import EvmAsm.Evm64.Exp.Compose.SavedBitBoundaryLoopFixed
public import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostIterPreCases

@[expose] public section

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

@[irreducible]
def expTwoMulFixedFirstIterCaseLoopPostWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) : Assertion :=
  expTwoMulFixedIterCaseLoopPost
    (256 : Word)
    (exponentWord.getLimbN 3)
    ((0 : Word) + signExtend12 (64 : BitVec 12))
    (evmSp + signExtend12 (56 : BitVec 12) +
      signExtend12 (-8 : BitVec 12))
    (exponentWord.getLimbN 2)
    sp (evmSp + signExtend12 (64 : BitVec 12))
    ((1 : EvmWord).getLimbN 0)
    ((1 : EvmWord).getLimbN 1)
    ((1 : EvmWord).getLimbN 2)
    ((1 : EvmWord).getLimbN 3)
    (baseWord.getLimbN 0) (baseWord.getLimbN 1)
    (baseWord.getLimbN 2) (baseWord.getLimbN 3)
    base **
  expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} :
    expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base =
      (expTwoMulFixedIterCaseLoopPost
        (256 : Word)
        (exponentWord.getLimbN 3)
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        base **
       expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) := by
  delta expTwoMulFixedFirstIterCaseLoopPostWithResidual
  rfl

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_pcFree
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} :
    (expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base).pcFree := by
  rw [expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedFirstIterCaseLoopPostWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    Assertion.PCFree
      (expTwoMulFixedFirstIterCaseLoopPostWithResidual
        sp evmSp baseWord exponentWord rest base) :=
  ⟨expTwoMulFixedFirstIterCaseLoopPostWithResidual_pcFree⟩

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_cases
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} {ps : PartialState}
    (h : expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      let rw := expTwoMulCondRw squareW
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix
        (256 : Word) sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        (expTwoMulIterCountNew (256 : Word) ≠ 0) **
        expTwoMulFixedIterScratchIs
          (evmSp + signExtend12 (64 : BitVec 12))
          v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          base) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix
        (256 : Word) sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (expTwoMulIterCountNew (256 : Word) ≠ 0) **
        expTwoMulFixedIterScratchIs
          (evmSp + signExtend12 (64 : BitVec 12))
          v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          (evmSp + signExtend12 (64 : BitVec 12))
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          base) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) := by
  rw [expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold] at h
  exact expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame h

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_pures
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} {ps : PartialState}
    (h : expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      let rw := expTwoMulCondRw squareW
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix
        (256 : Word) sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        (expTwoMulIterCountNew (256 : Word) ≠ 0) **
        expTwoMulFixedIterScratchIs
          (evmSp + signExtend12 (64 : BitVec 12))
          v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          base) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps ∧
      expTwoMulIterCountNew (256 : Word) ≠ 0 ∧
      ((0 : Word) + signExtend12 (64 : BitVec 12)) +
        signExtend12 (-1 : BitVec 12) = 0 ∧
      (exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) ≠ 0) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      ((expTwoMulFixedIterSkipCountPostScratchPrefix
        (256 : Word) sp (evmSp + signExtend12 (64 : BitVec 12))
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (expTwoMulIterCountNew (256 : Word) ≠ 0) **
        expTwoMulFixedIterScratchIs
          (evmSp + signExtend12 (64 : BitVec 12))
          v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          (evmSp + signExtend12 (64 : BitVec 12))
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          base) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps ∧
      expTwoMulIterCountNew (256 : Word) ≠ 0 ∧
      ((0 : Word) + signExtend12 (64 : BitVec 12)) +
        signExtend12 (-1 : BitVec 12) = 0 ∧
      (exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
        signExtend12 (0 : BitVec 12) = 0) := by
  rw [expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold] at h
  exact expTwoMulFixedIterCaseLoopPost_iterPre_or_reloadPointerFrame_pures h

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_no_reload
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} {ps : PartialState}
    (h : expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      let rw := expTwoMulCondRw squareW
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (expTwoMulIterCountNew (256 : Word))
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) := by
  rcases expTwoMulFixedFirstIterCaseLoopPostWithResidual_pures h with
    hCond | hRest
  · exact Or.inl hCond
  · rcases hRest with hSkip | hRest
    · exact Or.inr hSkip
    · rcases hRest with hReloadCond | hReloadSkip
      · rcases hReloadCond with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hFrame, h_count, h_c6, h_bit⟩
        rw [expTwoMulFixedFirstIterC6_decrement_eq] at h_c6
        contradiction
      · rcases hReloadSkip with
          ⟨v6, v7, v10, v11, d0, d1, d2, d3,
            hFrame, h_count, h_c6, h_bit⟩
        rw [expTwoMulFixedFirstIterC6_decrement_eq] at h_c6
        contradiction

theorem expTwoMulFixedFirstIterCaseLoopPostWithResidual_no_reload_norm
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} {ps : PartialState}
    (h : expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base ps) :
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      let rw := expTwoMulCondRw squareW
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (255 : Word)
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + 48)
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (255 : Word)
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + 48)
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) := by
  rcases expTwoMulFixedFirstIterCaseLoopPostWithResidual_no_reload h with
    hCond | hSkip
  · rcases hCond with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    refine Or.inl ⟨v6, v7, v10, v11, d0, d1, d2, d3, ?_⟩
    rwa [expTwoMulFixedFirstIterCountNew_eq,
      expTwoMulFixedFirstIterPointer_eq] at hPre
  · rcases hSkip with ⟨v6, v7, v10, v11, d0, d1, d2, d3, hPre⟩
    refine Or.inr ⟨v6, v7, v10, v11, d0, d1, d2, d3, ?_⟩
    rwa [expTwoMulFixedFirstIterCountNew_eq,
      expTwoMulFixedFirstIterPointer_eq] at hPre

@[irreducible]
def expTwoMulFixedSecondIterPreWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) : Assertion :=
  fun ps =>
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      let rw := expTwoMulCondRw squareW
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (255 : Word)
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + 48)
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (rw.getLimbN 3)
        (((base + 44) + 140) + 68)
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        d0 d1 d2 d3
        (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps) ∨
    (∃ v6 v7 v10 v11 d0 d1 d2 d3,
      let squareW :=
        expSquaringCallSquareW
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
      ((expTwoMulFixedIterPre
        (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
        v6
        (255 : Word)
        v10
        ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
          signExtend12 (0 : BitVec 12))
        (evmSp + 48)
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (squareW.getLimbN 3)
        (((base + 44) + 32) + 68)
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        d0 d1 d2 d3
        (squareW.getLimbN 0) (squareW.getLimbN 1)
        (squareW.getLimbN 2) (squareW.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11) **
        expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest) ps)

theorem expTwoMulFixedFirstCase_to_secondIterPreWithResidual
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} {ps : PartialState}
    (h : expTwoMulFixedFirstIterCaseLoopPostWithResidual
      sp evmSp baseWord exponentWord rest base ps) :
    expTwoMulFixedSecondIterPreWithResidual
      sp evmSp baseWord exponentWord rest base ps := by
  rw [expTwoMulFixedSecondIterPreWithResidual]
  exact expTwoMulFixedFirstIterCaseLoopPostWithResidual_no_reload_norm h

theorem expTwoMulFixedSecondIterPreWithResidual_pcFree
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word} :
    (expTwoMulFixedSecondIterPreWithResidual
      sp evmSp baseWord exponentWord rest base).pcFree := by
  intro hpc h_pre
  rw [expTwoMulFixedSecondIterPreWithResidual] at h_pre
  rcases h_pre with hCond | hSkip
  · rcases hCond with
      ⟨v6, v7, v10, v11, d0, d1, d2, d3, h_concrete_pre⟩
    exact
      pcFree_sepConj expTwoMulFixedIterPre_pcFree
        expTwoMulFixedFirstIterEntryResidual_pcFree hpc h_concrete_pre
  · rcases hSkip with
      ⟨v6, v7, v10, v11, d0, d1, d2, d3, h_concrete_pre⟩
    exact
      pcFree_sepConj expTwoMulFixedIterPre_pcFree
        expTwoMulFixedFirstIterEntryResidual_pcFree hpc h_concrete_pre

instance pcFreeInst_expTwoMulFixedSecondIterPreWithResidual
    (sp evmSp : Word)
    (baseWord exponentWord : EvmWord) (rest : List EvmWord)
    (base : Word) :
    Assertion.PCFree
      (expTwoMulFixedSecondIterPreWithResidual
        sp evmSp baseWord exponentWord rest base) :=
  ⟨expTwoMulFixedSecondIterPreWithResidual_pcFree⟩

theorem cpsTripleWithin_expTwoMulFixedSecondIterPreWithResidual
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {Q : Assertion}
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word}
    (hCond :
      ∀ v6 v7 v10 v11 d0 d1 d2 d3,
        let squareW :=
          expSquaringCallSquareW
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
        let rw := expTwoMulCondRw squareW
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        cpsTripleWithin nSteps entry exit_ cr
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
            v6
            (255 : Word)
            v10
            ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
              signExtend12 (0 : BitVec 12))
            (evmSp + 48)
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (rw.getLimbN 3)
            (((base + 44) + 140) + 68)
            (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
            (rw.getLimbN 3)
            d0 d1 d2 d3
            (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2)
            (rw.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          Q)
    (hSkip :
      ∀ v6 v7 v10 v11 d0 d1 d2 d3,
        let squareW :=
          expSquaringCallSquareW
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
        cpsTripleWithin nSteps entry exit_ cr
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3 <<< (1 : BitVec 6).toNat)
            v6
            (255 : Word)
            v10
            ((exponentWord.getLimbN 3 >>> (63 : BitVec 6).toNat) +
              signExtend12 (0 : BitVec 12))
            (evmSp + 48)
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (squareW.getLimbN 3)
            (((base + 44) + 32) + 68)
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            d0 d1 d2 d3
            (squareW.getLimbN 0) (squareW.getLimbN 1)
            (squareW.getLimbN 2) (squareW.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3) v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (expTwoMulFixedSecondIterPreWithResidual
        sp evmSp baseWord exponentWord rest base)
      Q := by
  intro R hR s hcr h_pre_R hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, h_pre, hRps⟩ := h_pre_R
  rw [expTwoMulFixedSecondIterPreWithResidual] at h_pre
  rcases h_pre with hCondPre | hSkipPre
  · rcases hCondPre with
      ⟨v6, v7, v10, v11, d0, d1, d2, d3, h_concrete_pre⟩
    exact hCond v6 v7 v10 v11 d0 d1 d2 d3 R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, h_concrete_pre, hRps⟩ hpc
  · rcases hSkipPre with
      ⟨v6, v7, v10, v11, d0, d1, d2, d3, h_concrete_pre⟩
    exact hSkip v6 v7 v10 v11 d0 d1 d2 d3 R hR s hcr
      ⟨hp, hcompat, psPre, psR, hdisj, hunion, h_concrete_pre, hRps⟩ hpc

theorem cpsTripleWithin_expTwoMulFixedFirstCase_to_secondIterPreWithResidual
    {nSteps : Nat} {entry exit_ : Word} {cr : CodeReq} {Q : Assertion}
    {sp evmSp : Word}
    {baseWord exponentWord : EvmWord} {rest : List EvmWord}
    {base : Word}
    (hTail :
      cpsTripleWithin nSteps entry exit_ cr
        (expTwoMulFixedSecondIterPreWithResidual
          sp evmSp baseWord exponentWord rest base)
        Q) :
    cpsTripleWithin nSteps entry exit_ cr
      (expTwoMulFixedFirstIterCaseLoopPostWithResidual
        sp evmSp baseWord exponentWord rest base)
      Q := by
  intro R hR s hcr h_pre_R hpc
  obtain ⟨hp, hcompat, psPre, psR, hdisj, hunion, h_pre, hRps⟩ := h_pre_R
  exact hTail R hR s hcr
    ⟨hp, hcompat, psPre, psR, hdisj, hunion,
      expTwoMulFixedFirstCase_to_secondIterPreWithResidual h_pre, hRps⟩
    hpc

theorem exp_two_mul_fixed_first_iter_to_secondIterPreWithResidual_spec_within
    {Q : Assertion}
    (sp evmSp v18 vOld v10 v7 v11 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (base : Word)
    (hbase : (base + 44 : Word) &&& 1 = 0)
    (hTail :
      cpsTripleWithin expTwoMulFixedFullLoopBodyTailBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedSecondIterPreWithResidual
          sp evmSp baseWord exponentWord rest base)
        Q) :
    cpsTripleWithin expTwoMulFixedFullLoopBodyBound
      (base + 44) (base + 296)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulFixedIterPre
        (exponentWord.getLimbN 3)
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (256 : Word)
        v10 v18
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (1 : Word) vOld
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (dWord.getLimbN 0) (dWord.getLimbN 1)
        (dWord.getLimbN 2) (dWord.getLimbN 3)
        (eWord.getLimbN 0) (eWord.getLimbN 1)
        (eWord.getLimbN 2) (eWord.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        v7 v11 **
       expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
      Q := by
  let residual := expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest
  let code := evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base
  have hStep :
      cpsNBranchWithin expTwoMulFixedReloadIterStepBound
        (base + 44)
        code
        (expTwoMulFixedIterPre
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (256 : Word)
          v10 v18
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          sp (evmSp + signExtend12 (64 : BitVec 12))
          (1 : Word) vOld
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
          (dWord.getLimbN 0) (dWord.getLimbN 1)
          (dWord.getLimbN 2) (dWord.getLimbN 3)
          (eWord.getLimbN 0) (eWord.getLimbN 1)
          (eWord.getLimbN 2) (eWord.getLimbN 3)
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          v7 v11)
        (expTwoMulFixedIterCaseExits
          (256 : Word)
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          sp (evmSp + signExtend12 (64 : BitVec 12))
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          base) := by
    exact
      exp_msb_bit_test_fixed_full_iter_case_posts_nbranch_evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode_spec_within
        (exponentWord.getLimbN 3)
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (256 : Word)
        v10 v18
        (evmSp + signExtend12 (56 : BitVec 12) +
          signExtend12 (-8 : BitVec 12))
        (exponentWord.getLimbN 2)
        sp (evmSp + signExtend12 (64 : BitVec 12))
        (1 : Word) vOld
        ((1 : EvmWord).getLimbN 0)
        ((1 : EvmWord).getLimbN 1)
        ((1 : EvmWord).getLimbN 2)
        ((1 : EvmWord).getLimbN 3)
        (dWord.getLimbN 0) (dWord.getLimbN 1)
        (dWord.getLimbN 2) (dWord.getLimbN 3)
        (eWord.getLimbN 0) (eWord.getLimbN 1)
        (eWord.getLimbN 2) (eWord.getLimbN 3)
        (baseWord.getLimbN 0) (baseWord.getLimbN 1)
        (baseWord.getLimbN 2) (baseWord.getLimbN 3)
        v7 v11 base hbase
  have hStepFramed :=
    cpsNBranchWithin_frameR
      (F := residual)
      (by
        dsimp [residual]
        exact expTwoMulFixedFirstIterEntryResidual_pcFree)
      hStep
  have hMerged :
      cpsTripleWithin
        (expTwoMulFixedReloadIterStepBound + expTwoMulFixedFullLoopBodyTailBound)
        (base + 44) (base + 296) code
        (expTwoMulFixedIterPre
          (exponentWord.getLimbN 3)
          ((0 : Word) + signExtend12 (64 : BitVec 12))
          (256 : Word)
          v10 v18
          (evmSp + signExtend12 (56 : BitVec 12) +
            signExtend12 (-8 : BitVec 12))
          (exponentWord.getLimbN 2)
          sp (evmSp + signExtend12 (64 : BitVec 12))
          (1 : Word) vOld
          ((1 : EvmWord).getLimbN 0)
          ((1 : EvmWord).getLimbN 1)
          ((1 : EvmWord).getLimbN 2)
          ((1 : EvmWord).getLimbN 3)
          (dWord.getLimbN 0) (dWord.getLimbN 1)
          (dWord.getLimbN 2) (dWord.getLimbN 3)
          (eWord.getLimbN 0) (eWord.getLimbN 1)
          (eWord.getLimbN 2) (eWord.getLimbN 3)
          (baseWord.getLimbN 0) (baseWord.getLimbN 1)
          (baseWord.getLimbN 2) (baseWord.getLimbN 3)
          v7 v11 ** residual)
        Q := by
    refine cpsNBranchWithin_merge hStepFramed ?_
    intro exit hmem
    cases hmem with
    | head =>
      dsimp [expTwoMulFixedIterCaseExits, residual, code]
      simpa [expTwoMulFixedFirstIterCaseLoopPostWithResidual_unfold] using
        cpsTripleWithin_expTwoMulFixedFirstCase_to_secondIterPreWithResidual
          (sp := sp) (evmSp := evmSp) (baseWord := baseWord)
          (exponentWord := exponentWord) (rest := rest) (base := base)
          hTail
    | tail _ hmem =>
      cases hmem with
      | head =>
        dsimp [expTwoMulFixedIterCaseExits, residual, code]
        refine
          cpsTripleWithin_mono_nSteps
            (Nat.zero_le expTwoMulFixedFullLoopBodyTailBound)
            (cpsTripleWithin_extend_code
              (cr := CodeReq.empty) (cr' := code) ?_ ?_)
        · intro a i h
          simp [CodeReq.empty] at h
        · refine cpsTripleWithin_refl ?_
          intro ps h_pre
          exfalso
          obtain ⟨_, _, _, _, h_exit, _⟩ := h_pre
          exact
            expTwoMulFixedIterCaseExitPost_nonzero_count_false
              expTwoMulFixedFirstIterCountNew_ne_zero h_exit
      | tail _ hmem =>
        cases hmem
  exact
    cpsTripleWithin_mono_nSteps
      expTwoMulFixedReloadIterStepBound_add_fullTail_le_full
      (by
        dsimp [residual, code] at hMerged
        exact hMerged)

/-- Fixed full-loop boundary wrapper whose loop body starts from the named
    existential first-iteration precondition produced by the fixed loop entry
    post. This is the surface needed before destructing the chosen
    `x10`/`x7`/`x11` scratch values for concrete first-iteration body proofs. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord (dWord :: eWord :: rest) exitCond base
    (fun _ h =>
      expTwoMulLoopEntryPostFixed_to_firstIterPreWithResidual h)
    hBody

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond) := by
    rw [expTwoMulFixedFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3
      baseWord exponentWord dWord eWord rest exitCond base hBodyNamed

/-- Fixed full-loop boundary wrapper whose loop body starts from the
    invariant-carrying first-iteration `PreN` residual assertion. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_pren_exists_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreNWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord (dWord :: eWord :: rest) exitCond base
    (fun _ h =>
      expTwoMulLoopEntryPostFixed_to_firstIterPreNWithResidual h)
    hBody

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_pren_exists_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_pren_exists_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      cpsTripleWithin 49408 (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreNWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) := by
  have hBodyNamed :
      cpsTripleWithin expTwoMulFixedFullLoopBodyBound
        (base + 44) (base + 296)
        (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
        (expTwoMulFixedFirstIterPreNWithResidual sp evmSp v18 vOld
          baseWord exponentWord dWord eWord rest)
        (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
          r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
          exitCond) := by
    rw [expTwoMulFixedFullLoopBodyBound_eq]
    exact hBody
  rw [← expTwoMulFixedFullLoopBoundaryBound_eq]
  exact
    exp_two_mul_fixed_full_loop_boundary_of_entry_pren_exists_body_general_spec_within
      sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3
      baseWord exponentWord dWord eWord rest exitCond base hBodyNamed

/-- Fixed full-loop boundary wrapper whose body proof is supplied for every
    concrete choice of the first-iteration scratch registers. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin expTwoMulFixedFullLoopBodyBound
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
            baseWord exponentWord dWord eWord **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual hBody)

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin 49408
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedFirstIterPre sp evmSp v10 v18 vOld v7 v11
            baseWord exponentWord dWord eWord **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_exists_body_general_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (cpsTripleWithin_expTwoMulFixedFirstIterPreWithResidual hBody)

/-- Fixed full-loop boundary wrapper whose body proof is phrased directly over
    the canonical `expTwoMulFixedIterPre` arguments for the first iteration. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin expTwoMulFixedFullLoopBodyBound
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3)
            ((0 : Word) + signExtend12 (64 : BitVec 12))
            (256 : Word)
            v10 v18
            (evmSp + signExtend12 (56 : BitVec 12) +
              signExtend12 (-8 : BitVec 12))
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (1 : Word) vOld
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
            (dWord.getLimbN 0) (dWord.getLimbN 1)
            (dWord.getLimbN 2) (dWord.getLimbN 3)
            (eWord.getLimbN 0) (eWord.getLimbN 1)
            (eWord.getLimbN 2) (eWord.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3)
            v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin expTwoMulFixedFullLoopBoundaryBound base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (fun v10 v7 v11 => by
      rw [expTwoMulFixedFirstIterPre_unfold]
      exact hBody v10 v7 v11)

/-- Closed-bound variant of
    `exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_spec_within`. -/
theorem exp_two_mul_fixed_full_loop_boundary_of_entry_iterpre_body_general_closed_bound_spec_within
    (sp evmSp cOld tOld c6Old c16Old c19Old
      m0 m1 m2 m3 vOld v18 iterCountNew
      r0 r1 r2 r3 d0 d1 d2 d3 : Word)
    (baseWord exponentWord dWord eWord : EvmWord) (rest : List EvmWord)
    (exitCond : Prop) (base : Word)
    (hBody :
      ∀ v10 v7 v11,
        cpsTripleWithin 49408
          (base + 44) (base + 296)
          (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
          (expTwoMulFixedIterPre
            (exponentWord.getLimbN 3)
            ((0 : Word) + signExtend12 (64 : BitVec 12))
            (256 : Word)
            v10 v18
            (evmSp + signExtend12 (56 : BitVec 12) +
              signExtend12 (-8 : BitVec 12))
            (exponentWord.getLimbN 2)
            sp (evmSp + signExtend12 (64 : BitVec 12))
            (1 : Word) vOld
            ((1 : EvmWord).getLimbN 0)
            ((1 : EvmWord).getLimbN 1)
            ((1 : EvmWord).getLimbN 2)
            ((1 : EvmWord).getLimbN 3)
            (dWord.getLimbN 0) (dWord.getLimbN 1)
            (dWord.getLimbN 2) (dWord.getLimbN 3)
            (eWord.getLimbN 0) (eWord.getLimbN 1)
            (eWord.getLimbN 2) (eWord.getLimbN 3)
            (baseWord.getLimbN 0) (baseWord.getLimbN 1)
            (baseWord.getLimbN 2) (baseWord.getLimbN 3)
            v7 v11 **
           expTwoMulFixedFirstIterEntryResidual evmSp exponentWord rest)
          (expTwoMulLoopExitFullStackPreFrame sp evmSp iterCountNew tOld
            r0 r1 r2 r3 d0 d1 d2 d3 baseWord (dWord :: eWord :: rest)
            exitCond)) :
    cpsTripleWithin 49429 base (base + 336)
      (evmExpMsbSavedBitTwoMulFixedCanonicalAppendedMulCode base)
      (expTwoMulBoundaryPreFixed sp evmSp cOld tOld c6Old c16Old c19Old
        m0 m1 m2 m3 vOld v18 baseWord exponentWord (dWord :: eWord :: rest))
      (expTwoMulLoopExitPost sp evmSp iterCountNew r0 r1 r2 r3
        baseWord (dWord :: eWord :: rest) exitCond) :=
  exp_two_mul_fixed_full_loop_boundary_of_entry_concrete_body_general_closed_bound_spec_within
    sp evmSp cOld tOld c6Old c16Old c19Old
    m0 m1 m2 m3 vOld v18 iterCountNew
    r0 r1 r2 r3 d0 d1 d2 d3
    baseWord exponentWord dWord eWord rest exitCond base
    (fun v10 v7 v11 => by
      rw [expTwoMulFixedFirstIterPre_unfold]
      exact hBody v10 v7 v11)

end EvmAsm.Evm64.Exp.Compose
