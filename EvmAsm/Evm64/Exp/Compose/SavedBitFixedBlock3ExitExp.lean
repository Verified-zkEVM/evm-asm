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

end EvmAsm.Evm64.Exp.Compose
