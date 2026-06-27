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
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step

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

/-- Reload-boundary re-partition (cond branch, block 1). -/
theorem expTwoMulFixedIterReloadCondCountPost_residual_repartition_one
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 1 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 0) sp evmSp
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
        (expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord **
         frame))) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadCondCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_succ_one] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterReloadCondScratchFrame_to_iterPre_frame
    (nextNextLimb := exponentWord.getLimbN 0)
    (frame := expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
      lookahead exponentWord ** frame)
  have hCombined :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix e c6 ptr nextLimb base) **
       (((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 0) **
        expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord) **
        frame)) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  xperm_hyp hCombined

/-- Reload-boundary re-partition (skip branch, block 1). -/
theorem expTwoMulFixedIterReloadSkipCountPost_residual_repartition_one
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 1 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        (ptr + signExtend12 (-8 : BitVec 12)) (exponentWord.getLimbN 0) sp evmSp
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
        (expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord **
         frame))) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadSkipCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_succ_one] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterReloadSkipScratchFrame_to_iterPre_frame
    (nextNextLimb := exponentWord.getLimbN 0)
    (frame := expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
      lookahead exponentWord ** frame)
  have hCombined :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix e c6 ptr nextLimb
          evmSp a0 a1 a2 a3 base) **
       (((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 0) **
        expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
          lookahead exponentWord) **
        frame)) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  xperm_hyp hCombined

/-- Reload-boundary re-partition (cond branch, block 2 → block 3): the b=2 reload
    advances `x16` to `ptr-8 = evmSp+se(-40)` = base operand `a3`'s address, so it
    enters the RELAXED block-3 pre (`x16` register only, base `a3` is the cell at
    that address, no separate pointer cell).  `ExpResidual 2 = emp`. -/
theorem expTwoMulFixedIterReloadCondCountPost_residual_repartition_two
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (hptr : ptr + signExtend12 (-8 : BitVec 12)
      = evmSp + signExtend12 (-40 : BitVec 12))
    (h :
      (expTwoMulFixedIterReloadCondCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 2 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPreRelaxedBlock3
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        sp evmSp
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
       (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadCondCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_ge_two (by omega), sepConj_emp_left'] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  have hC :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadCondCountPostScratchSuffix e c6 ptr nextLimb base) **
        frame) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  obtain ⟨h_exit, h_c6, h_bit⟩ :=
    expTwoMulFixedIterReloadCondScratchFrame_pures hC
  replace hC := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ hC
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterReloadCondCountPostScratchSuffix
    expTwoMulFixedIterSkipCondRestScratchSuffix
    expTwoMulFixedIterReloadCondFrame at hC
  simp only [] at hC
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at hC
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at hC
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ :
        Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at hC
  simp only [sepConj_emp_left', sepConj_emp_right'] at hC
  rw [hptr] at hC
  unfold expTwoMulFixedIterPreRelaxedBlock3
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (140 : Word) + 68 = 208 from by decide,
    show (44 : Word) + 208 = 252 from by decide,
    BitVec.add_assoc] at hC ⊢
  xperm_hyp hC

/-- Reload-boundary re-partition (skip branch, block 2). -/
theorem expTwoMulFixedIterReloadSkipCountPost_residual_repartition_two
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (hptr : ptr + signExtend12 (-8 : BitVec 12)
      = evmSp + signExtend12 (-40 : BitVec 12))
    (h :
      (expTwoMulFixedIterReloadSkipCountPost iterCount e c6 ptr nextLimb sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
       (expTwoMulFixedExpResidual 2 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPreRelaxedBlock3
        nextLimb
        ((0 : Word) + signExtend12 (64 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        sp evmSp
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
       (((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb) ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterReloadSkipCountPost_choose_scratch hA
  rw [expTwoMulFixedExpResidual_ge_two (by omega), sepConj_emp_left'] at hR
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  have hC :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterReloadSkipCountPostScratchSuffix e c6 ptr nextLimb
          evmSp a0 a1 a2 a3 base) **
        frame) ps :=
    ⟨psA, psR, hdisj, hunion, hScratch, hR⟩
  obtain ⟨h_exit, h_c6, h_bit⟩ :=
    expTwoMulFixedIterReloadSkipScratchFrame_pures hC
  replace hC := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ hC
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterReloadSkipCountPostScratchSuffix
    expTwoMulFixedIterReloadSkipRestScratchSuffix
    expTwoMulFixedIterBaseFrame at hC
  simp only [] at hC
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at hC
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at hC
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ :
        Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at hC
  simp only [sepConj_emp_left', sepConj_emp_right'] at hC
  rw [hptr] at hC
  unfold expTwoMulFixedIterPreRelaxedBlock3
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (32 : Word) + 68 = 100 from by decide,
    show (44 : Word) + 100 = 144 from by decide,
    BitVec.add_assoc] at hC ⊢
  xperm_hyp hC

/-- Non-reload (within-block) re-partition, cond branch: the loop-back
    `SkipCondCountPost ** PointerPost` together with the (unchanged) exponent
    residual produces the next iteration's `IterPre` (same pointer/block) framed
    by the same residual.  The exponent residual rides untouched — only the
    scratch/pointer cells are reshaped into the next `IterPre`. -/
theorem expTwoMulFixedIterSkipCondCountPost_residual_repartition
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {b : Nat} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        expTwoMulFixedIterPointerPost ptr nextLimb) **
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
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
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨psC, psP, hdisjCP, hunionCP, hCount, hPtr⟩ := hA
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterSkipCondCountPost_choose_scratch hCount
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame
    (frame := expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)
  rw [expTwoMulFixedIterPointerFrame_unfold]
  have hCombined :
      (((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base) **
        expTwoMulFixedIterPointerPost ptr nextLimb) **
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps :=
    ⟨psA, psR, hdisj, hunion,
      ⟨psC, psP, hdisjCP, hunionCP, hScratch, hPtr⟩, hR⟩
  xperm_hyp hCombined

/-- Non-reload (within-block) re-partition, skip branch. -/
theorem expTwoMulFixedIterSkipCountPost_residual_repartition
    {iterCount e c6 ptr nextLimb sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {b : Nat} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        expTwoMulFixedIterPointerPost ptr nextLimb) **
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPre
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        ptr nextLimb sp evmSp
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
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨psC, psP, hdisjCP, hunionCP, hCount, hPtr⟩ := hA
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterSkipCountPost_choose_scratch hCount
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame
    (frame := expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)
  rw [expTwoMulFixedIterPointerFrame_unfold]
  have hCombined :
      (((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base) **
        expTwoMulFixedIterPointerPost ptr nextLimb) **
       (expTwoMulFixedExpResidual b ptr lookahead exponentWord ** frame)) ps :=
    ⟨psA, psR, hdisj, hunion,
      ⟨psC, psP, hdisjCP, hunionCP, hScratch, hPtr⟩, hR⟩
  xperm_hyp hCombined

/-- Relaxed (block-3) variant of `expTwoMulFixedIterSkipCondScratchFrame_pures`:
    the loop pointer frame is the concrete `x16 ↦ evmSp+se(-40)` (no separate
    pointer cell), but the pures (`exitCond`, `c6New≠0`, `bit≠0`) live in the
    scratch prefix/suffix and are extracted identically. -/
theorem expTwoMulFixedIterSkipCondScratchFrame_relaxedBlock3_pures
    {iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0 := by
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondCountPostScratchSuffix
    expTwoMulFixedIterSkipCondFrame at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffixPtr, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffixPtr⟩ := hTail
  obtain ⟨_psSuffix, _psPtr, _hDisjointSuffix, _hUnionSuffix,
    hSuffix, _hPtr⟩ := hSuffixPtr
  obtain ⟨_psRet, _psSkipCondFrame, _hDisjointRet, _hUnionRet,
    _hRet, hSkipCondFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hX20Tail⟩ := hSkipCondFrame
  obtain ⟨_, _, _, _, _, hFrameTail⟩ := hX20Tail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hFrameTail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨h_exit, h_c6, h_bit⟩

/-- Relaxed (block-3) variant of
    `expTwoMulFixedIterSkipCondScratchFrame_to_iterPre_frame`: assemble the cond
    scratch decomposition plus the concrete `x16 ↦ evmSp+se(-40)` pointer
    register (no pointer cell) into the next iteration's
    `expTwoMulFixedIterPreRelaxedBlock3`. -/
theorem expTwoMulFixedIterSkipCondScratchFrame_to_iterPreRelaxedBlock3_frame
    {iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base **
          (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    let rw := expTwoMulCondRw squareW a0 a1 a2 a3
    ((expTwoMulFixedIterPreRelaxedBlock3
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      sp evmSp
      (rw.getLimbN 3)
      (((base + 44) + 140) + 68)
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      d0 d1 d2 d3
      (rw.getLimbN 0) (rw.getLimbN 1) (rw.getLimbN 2) (rw.getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      frame) ps := by
  intro squareW rw
  have h_pures := expTwoMulFixedIterSkipCondScratchFrame_relaxedBlock3_pures h
  rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  unfold expTwoMulFixedIterSkipCondCountPostScratchPrefix
    expTwoMulFixedIterSkipCondRestScratchPrefix
    expTwoMulFixedIterSkipCondCountPostScratchSuffix
    expTwoMulFixedIterSkipCondRestScratchSuffix
    expTwoMulFixedIterSkipCondFrame at h
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ :
        Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  unfold expTwoMulFixedIterPreRelaxedBlock3
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    show (140 : Word) + 68 = 208 from by decide,
    show (44 : Word) + 208 = 252 from by decide,
    BitVec.add_assoc] at h ⊢
  xperm_hyp h

/-- Non-reload (within-block) re-partition, cond branch, block 3: the relaxed
    cond `CountPost` (with the concrete `x16 ↦ evmSp+se(-40)` pointer, no pointer
    cell) plus the block-3 (empty) residual re-partition into the next
    iteration's `expTwoMulFixedIterPreRelaxedBlock3`. -/
theorem expTwoMulFixedIterSkipCondCountPost_residual_repartition_block3
    {iterCount e c6 ptr sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCondCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPreRelaxedBlock3
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        sp evmSp
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
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨psC, psP, hdisjCP, hunionCP, hCount, hPtr⟩ := hA
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterSkipCondCountPost_choose_scratch hCount
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterSkipCondScratchFrame_to_iterPreRelaxedBlock3_frame
    (frame := expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)
  have hCombined :
      (((expTwoMulFixedIterSkipCondCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 a0 a1 a2 a3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCondCountPostScratchSuffix e c6 base) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps :=
    ⟨psA, psR, hdisj, hunion,
      ⟨psC, psP, hdisjCP, hunionCP, hScratch, hPtr⟩, hR⟩
  xperm_hyp hCombined

/-- Relaxed (block-3) variant of `expTwoMulFixedIterSkipScratchFrame_pures`. -/
theorem expTwoMulFixedIterSkipScratchFrame_relaxedBlock3_pures
    {iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))) **
        frame) ps) :
    exitCond ∧
    c6 + signExtend12 (-1 : BitVec 12) ≠ 0 ∧
    (e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0 := by
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipCountPostScratchSuffix
    expTwoMulFixedIterSkipRestScratchSuffix at h
  obtain ⟨psMain, _psFrame, _hDisjoint, _hUnion, hMain, _hFrame⟩ := h
  obtain ⟨psPrefix, _psTail, _hDisjointPrefix, _hUnionPrefix, hPrefix, hTail⟩ :=
    hMain
  obtain ⟨psCount, _psRest, _hDisjointCount, _hUnionCount, hCount, _hRest⟩ :=
    hPrefix
  obtain ⟨_psX9, _psX0Exit, _hDisjointX9, _hUnionX9, _hX9, hX0Exit⟩ :=
    hCount
  obtain ⟨_psX0, _psExit, _hDisjointX0, _hUnionX0, _hX0, hExit⟩ :=
    hX0Exit
  have h_exit : exitCond := hExit.2
  obtain ⟨_psScratch, _psSuffixPtr, _hDisjointScratch, _hUnionScratch,
    _hScratch, hSuffixPtr⟩ := hTail
  obtain ⟨_psSuffix, _psPtr, _hDisjointSuffix, _hUnionSuffix,
    hSuffix, _hPtr⟩ := hSuffixPtr
  obtain ⟨_psSkipRest, _psBaseFrame, _hDisjointSkipRest, _hUnionSkipRest,
    hSkipRest, _hBaseFrame⟩ := hSuffix
  obtain ⟨_, _, _, _, _, hSkipRestTail⟩ := hSkipRest
  obtain ⟨_, _, _, _, _, hX20Tail⟩ := hSkipRestTail
  obtain ⟨_, _, _, _, _, hX18Tail⟩ := hX20Tail
  obtain ⟨_, _, _, _, _, hPureTail⟩ := hX18Tail
  have h_c6 : c6 + signExtend12 (-1 : BitVec 12) ≠ 0 :=
    ((sepConj_pure_left _).1 hPureTail).1
  obtain ⟨_, h_bit⟩ := ((sepConj_pure_left _).1 hPureTail).2
  exact ⟨h_exit, h_c6, h_bit⟩

/-- Relaxed (block-3) variant of
    `expTwoMulFixedIterSkipScratchFrame_to_iterPre_frame`. -/
theorem expTwoMulFixedIterSkipScratchFrame_to_iterPreRelaxedBlock3_frame
    {iterCount e c6 sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {v6 v7 v10 v11 d0 d1 d2 d3 : Word}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
        r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        (expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base **
          (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12))))) **
        frame) ps) :
    let squareW := expSquaringCallSquareW r0 r1 r2 r3
    ((expTwoMulFixedIterPreRelaxedBlock3
      (e <<< (1 : BitVec 6).toNat)
      (c6 + signExtend12 (-1 : BitVec 12))
      (expTwoMulIterCountNew iterCount)
      v10
      ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
      sp evmSp
      (squareW.getLimbN 3)
      (((base + 44) + 32) + 68)
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      d0 d1 d2 d3
      (squareW.getLimbN 0) (squareW.getLimbN 1)
      (squareW.getLimbN 2) (squareW.getLimbN 3)
      a0 a1 a2 a3 v7 v11) **
      frame) ps := by
  intro squareW
  have h_pures := expTwoMulFixedIterSkipScratchFrame_relaxedBlock3_pures h
  rcases h_pures with ⟨h_exit, h_c6, h_bit⟩
  replace h := sepConj_mono_left
    (sepConj_mono_right (sepConj_mono_left
      expTwoMulFixedIterScratchIs_x6_to_regOwn)) _ h
  unfold expTwoMulFixedIterSkipCountPostScratchPrefix
    expTwoMulFixedIterSkipRestScratchPrefix
    expTwoMulFixedIterSkipCountPostScratchSuffix
    expTwoMulFixedIterSkipRestScratchSuffix
    expTwoMulFixedIterBaseFrame at h
  rw [show (⌜exitCond⌝ : Assertion) = empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_exit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  rw [show (⌜c6 + signExtend12 (-1 : BitVec 12) ≠ 0⌝ : Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_c6⟩⟩] at h
  rw [show
      (⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ :
        Assertion) =
      empAssertion from
      funext fun ps' => propext ⟨fun h' => h'.1, fun h' => ⟨h', h_bit⟩⟩] at h
  simp only [sepConj_emp_right'] at h
  unfold expTwoMulFixedIterPreRelaxedBlock3
  simp only [evmWordIs, signExtend12_0, signExtend12_8, signExtend12_16,
    signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48,
    signExtend12_56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg64,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg56,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg48,
    EvmAsm.Evm64.Exp.AddrNorm.exp_se12_neg40,
    EvmAsm.Rv64.AddrNorm.word_add_zero,
    show (32 : Word) + 8 = 40 from by decide,
    show (32 : Word) + 16 = 48 from by decide,
    show (32 : Word) + 24 = 56 from by decide,
    BitVec.add_assoc] at h ⊢
  xperm_hyp h

/-- Non-reload (within-block) re-partition, skip branch, block 3. -/
theorem expTwoMulFixedIterSkipCountPost_residual_repartition_block3
    {iterCount e c6 ptr sp evmSp
      r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {exitCond : Prop} {lookahead : Word} {exponentWord : EvmWord}
    {frame : Assertion} {ps : PartialState}
    (h :
      ((expTwoMulFixedIterSkipCountPost iterCount e c6 sp evmSp
        r0 r1 r2 r3 a0 a1 a2 a3 base exitCond **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps) :
    (∃ v7 v10 v11 d0 d1 d2 d3,
      (expTwoMulFixedIterPreRelaxedBlock3
        (e <<< (1 : BitVec 6).toNat)
        (c6 + signExtend12 (-1 : BitVec 12))
        (expTwoMulIterCountNew iterCount)
        v10
        ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))
        sp evmSp
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
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps) := by
  obtain ⟨psA, psR, hdisj, hunion, hA, hR⟩ := h
  obtain ⟨psC, psP, hdisjCP, hunionCP, hCount, hPtr⟩ := hA
  obtain ⟨v6, v7, v10, v11, d0, d1, d2, d3, hScratch⟩ :=
    expTwoMulFixedIterSkipCountPost_choose_scratch hCount
  refine ⟨v7, v10, v11, d0, d1, d2, d3, ?_⟩
  apply expTwoMulFixedIterSkipScratchFrame_to_iterPreRelaxedBlock3_frame
    (frame := expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)
  have hCombined :
      (((expTwoMulFixedIterSkipCountPostScratchPrefix iterCount sp evmSp
          r0 r1 r2 r3 exitCond **
        expTwoMulFixedIterScratchIs evmSp v6 v7 v10 v11 d0 d1 d2 d3 **
        expTwoMulFixedIterSkipCountPostScratchSuffix e c6 evmSp
          a0 a1 a2 a3 base) **
        (.x16 ↦ᵣ (evmSp + signExtend12 (-40 : BitVec 12)))) **
       (expTwoMulFixedExpResidual 3 ptr lookahead exponentWord ** frame)) ps :=
    ⟨psA, psR, hdisj, hunion,
      ⟨psC, psP, hdisjCP, hunionCP, hScratch, hPtr⟩, hR⟩
  xperm_hyp hCombined

end EvmAsm.Evm64.Exp.Compose
