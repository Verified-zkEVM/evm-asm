/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedBlock3ExitExp

  Exit-result pinning for the block-3 final iteration (k = 255).

  At the loop exit the result cells hold the final accumulator step:
  `expTwoMulCondRw (squareW …) …` on the cond branch (bit 255 = 1) and
  `expSquaringCallSquareW …` on the skip branch (bit 255 = 0).  Given the
  accumulator invariant at k = 255, both collapse — via the proven
  per-branch accumulator-succ lemma + `…_full` — to `EvmWord.exp base exponent`.

  These are the semantic-pinning facts the final-chain `hExitU` discharge needs:
  they turn the branch-dependent spatial exit result into the single fixed
  `EvmWord.exp base exponent`.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedBlock3Step
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant
import EvmAsm.Evm64.Exp.Compose.SavedBitFixedRelaxedExitBridge

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Cond-branch (bit 255 = 1) final exit result is `EvmWord.exp`. -/
theorem expTwoMulFixedBlock3FinalCondResultEqExp
    {baseWord exponentWord : EvmWord}
    {e a0 a1 a2 a3 r0 r1 r2 r3 : Word}
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord 255 e)
    (hBitNe :
      e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) ≠ 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255
        r0 r1 r2 r3) :
    expResultWord
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 0)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 1)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 2)
      ((expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3).getLimbN 3)
      = EvmWord.exp baseWord exponentWord :=
  expTwoMulFixedAccumulatorInvariant_full
    (expTwoMulFixedAccumulatorInvariant_succ_of_condRw_cursor_branch
      (by decide) hBase hCursor hBitNe hInv)

/-- Skip-branch (bit 255 = 0) final exit result is `EvmWord.exp`. -/
theorem expTwoMulFixedBlock3FinalSkipResultEqExp
    {baseWord exponentWord : EvmWord}
    {e r0 r1 r2 r3 : Word}
    (hCursor : expTwoMulFixedCursorInvariant exponentWord 255 e)
    (hBitZero :
      e >>> (63 : BitVec 6).toNat + signExtend12 (0 : BitVec 12) = 0)
    (hInv :
      expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255
        r0 r1 r2 r3) :
    expResultWord
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 0)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 1)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 2)
      ((expSquaringCallSquareW r0 r1 r2 r3).getLimbN 3)
      = EvmWord.exp baseWord exponentWord :=
  expTwoMulFixedAccumulatorInvariant_full
    (expTwoMulFixedAccumulatorInvariant_succ_of_squareW_cursor_branch
      (by decide) hCursor hBitZero hInv)

/-- Relaxed block-3 reload merged exit (cond ∨ skip) + ambient exponent frame →
    full-stack exit pre-frame with the result pinned to `EvmWord.exp base exponent`.
    Both bit-branches collapse to the same fixed result via the per-branch pinning
    helpers (`expTwoMulFixedBlock3FinalCond/SkipResultEqExp`), with the leftover
    `x1` value existentially quantified.  This is the relaxed analog of
    `expTwoMulIterExitPost_to_FullStackPreFrame_framed`. -/
theorem expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload_to_FullStackPreFrame_exp_framed
    {e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {baseWord exponentWord : EvmWord} {ps : PartialState}
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord 255 e)
    (hInv : expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3)
    (h : (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 vx1 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, EvmWord.exp baseWord exponentWord]
          (expTwoMulIterCountNew iterCount = 0) **
       (.x19 ↦ᵣ a3) **
       (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
       (.x18 ↦ᵣ (e >>> (63 : BitVec 6).toNat)) **
       (.x16 ↦ᵣ (evmSp + (18446744073709551576 + signExtend12 (-8 : BitVec 12)))) **
       (.x1 ↦ᵣ vx1) **
       regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  obtain ⟨w0, w1, w2, w3, hbridge⟩ :=
    expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload_to_FullStackPreFrame h
  rcases hbridge with ⟨hc, hbit⟩ | ⟨hs, hbit⟩
  · -- cond branch (bit ≠ 0): result = rw, pinned to EvmWord.exp
    have hrw :
        expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3
          = EvmWord.exp baseWord exponentWord := by
      rw [← expResultWord_getLimbN_self
        (expTwoMulCondRw (expSquaringCallSquareW r0 r1 r2 r3) a0 a1 a2 a3)]
      exact expTwoMulFixedBlock3FinalCondResultEqExp hBase hCursor
        (by rw [signExtend12_0, EvmAsm.Rv64.AddrNorm.word_add_zero]; exact hbit) hInv
    refine ⟨w0, w1, w2, w3, ((base + 44) + 140) + 68, ?_⟩
    rw [← hrw]; exact hc
  · -- skip branch (bit = 0): result = squareW, pinned to EvmWord.exp
    have hsq :
        expSquaringCallSquareW r0 r1 r2 r3 = EvmWord.exp baseWord exponentWord := by
      rw [← expResultWord_getLimbN_self (expSquaringCallSquareW r0 r1 r2 r3)]
      exact expTwoMulFixedBlock3FinalSkipResultEqExp hCursor
        (by rw [signExtend12_0, EvmAsm.Rv64.AddrNorm.word_add_zero]; exact hbit) hInv
    refine ⟨w0, w1, w2, w3, ((base + 44) + 32) + 68, ?_⟩
    rw [← hsq]; exact hs

/-- `…_exp_framed` with the five concrete leftover registers weakened to `regOwn`.
    This is the unified leftover frame `L_own` (all nine leftover registers as
    `regOwn`) that the final-chain `hExitU_relaxed` discharge feeds to the
    leftover-aware boundary brick — weak enough that *both* the relaxed and the
    (future) standard merged exit branches imply it. -/
theorem expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload_to_FullStackPreFrame_exp_regown
    {e c6 iterCount sp evmSp r0 r1 r2 r3 a0 a1 a2 a3 base : Word}
    {baseWord exponentWord : EvmWord} {ps : PartialState}
    (hBase : baseWord = expResultWord a0 a1 a2 a3)
    (hCursor : expTwoMulFixedCursorInvariant exponentWord 255 e)
    (hInv : expTwoMulFixedAccumulatorInvariant baseWord exponentWord 255 r0 r1 r2 r3)
    (h : (expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload e c6 iterCount sp evmSp
            r0 r1 r2 r3 a0 a1 a2 a3 base **
          evmWordIs (evmSp + signExtend12 ((-32) : BitVec 12)) exponentWord) ps) :
    ∃ w0 w1 w2 w3 : Word,
      (expTwoMulLoopExitFullStackPreFrame sp (evmSp - 64)
          (expTwoMulIterCountNew iterCount)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          ((EvmWord.exp baseWord exponentWord).getLimbN 0)
          ((EvmWord.exp baseWord exponentWord).getLimbN 1)
          ((EvmWord.exp baseWord exponentWord).getLimbN 2)
          ((EvmWord.exp baseWord exponentWord).getLimbN 3)
          (exponentWord.getLimbN 0) (exponentWord.getLimbN 1)
          (exponentWord.getLimbN 2) (exponentWord.getLimbN 3)
          (expResultWord a0 a1 a2 a3)
          [expResultWord w0 w1 w2 w3, EvmWord.exp baseWord exponentWord]
          (expTwoMulIterCountNew iterCount = 0) **
       regOwn .x19 ** regOwn .x20 ** regOwn .x18 ** regOwn .x16 **
       regOwn .x1 ** regOwn .x6 ** regOwn .x7 ** regOwn .x10 ** regOwn .x11) ps := by
  obtain ⟨w0, w1, w2, w3, vx1, hfs⟩ :=
    expTwoMulFixedIterMergedExitPostRelaxedBlock3Reload_to_FullStackPreFrame_exp_framed
      hBase hCursor hInv h
  refine ⟨w0, w1, w2, w3, ?_⟩
  exact sepConj_mono_right
    (sepConj_mono (regIs_to_regOwn .x19 a3)
      (sepConj_mono (regIs_to_regOwn .x20 _)
        (sepConj_mono (regIs_to_regOwn .x18 _)
          (sepConj_mono (regIs_to_regOwn .x16 _)
            (sepConj_mono_left (regIs_to_regOwn .x1 vx1)))))) _ hfs

end EvmAsm.Evm64.Exp.Compose
