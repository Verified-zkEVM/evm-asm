/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadResidualRepartition

  Reload-boundary re-partition: combine the merged loop-back reload `CountPost`
  with the exponent residual `expTwoMulFixedExpResidual` to produce the next
  iteration's `expTwoMulFixedIterPre`, with the residual shrunk by one block.

  This packages, for the `ExpResidual`-threaded merged induction's reload case:
  `_choose_scratch` (expose the reload scratch) + the `_succ_zero` residual split
  (expose the `ptr-8` look-ahead cell) + the proven reload→IterPre assembler.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadReshuffle
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Reload-boundary re-partition (cond branch, block 0): the reload `CountPost`
    plus the block-0 exponent residual re-partition into the next iteration's
    `IterPre` (cursor reloaded from the `ptr-8` cell, pointer advanced) framed by
    the block-1 residual and the now-stale pointer cell. -/
theorem expTwoMulFixedIterReloadCondCountPost_residual_repartition_zero
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 0 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 1) sp evmSp
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
        (((base + 44) + 140) + 68)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
        d0 d1 d2 d3
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
        ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
        a0 a1 a2 a3 v7 v11 **
       (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord **
         frame))) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadCondCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_succ_zero] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterReloadCondScratchFrame_to_iterPre_frame
    (nextNextLimb := exponentWord.getLimbN 1)
    (frame := expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
      lookahead exponentWord ** frame)
  have hCombined :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix e c6 ptr nextLimb base) **
       (((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 1) **
        expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord) **
        frame)) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  xperm_hyp hCombined

/-- Reload-boundary re-partition (skip branch, block 0): the skip analogue of
    `expTwoMulFixedIterReloadCondCountPost_residual_repartition_zero`. -/
theorem expTwoMulFixedIterReloadSkipCountPost_residual_repartition_zero
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 0 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 1) sp evmSp
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
        (((base + 44) + 32) + 68)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
        d0 d1 d2 d3
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
        ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
        a0 a1 a2 a3 v7 v11 **
       (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) **
        (expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord **
         frame))) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadSkipCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_succ_zero] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterReloadSkipScratchFrame_to_iterPre_frame
    (nextNextLimb := exponentWord.getLimbN 1)
    (frame := expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
      lookahead exponentWord ** frame)
  have hCombined :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix e c6 ptr nextLimb
          evmSp a0 a1 a2 a3 base) **
       (((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 1) **
        expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord) **
        frame)) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  xperm_hyp hCombined

end EvmAsm.Evm64.Exp.Compose
