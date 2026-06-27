/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual

  The exponent residual `ExpResidual` carried (as a framed pcFree assertion)
  by the merged-loop induction: the not-yet-loaded limb cells strictly below
  the loop pointer `x16 = ptr`, organized by block `b = k / 64`.

  Within a block the pointer `x16` is constant, so `ExpResidual` is constant
  (it depends only on the block `b` and `ptr`).  At each of the first two
  64-bit reload boundaries the pointer advances by `-8`, the top residual cell
  becomes the next iteration's `IterPre` pointer cell (consumed by the proven
  reload assemblers), and the (now stale) old pointer cell drops into the
  read-only ambient frame.  The residual therefore shrinks by one cell per
  reload.

  Cell counts are `2 / 1 / 0 / 0` by block.  Block 0 (`x16 = OUTER+48`) carries
  the two exponent cells strictly below `x16` that the next two reloads will
  consume: `OUTER+40` (`getLimbN 1`) and `OUTER+32` (`getLimbN 0`).  Block 1
  drops the top cell, and blocks 2/3 carry nothing.

  Block 3's spurious final reload reads base operand `a3` (the over-walk cell
  just below the exponent), which is handled by the *relaxed* block-3 engine
  (`SavedBitFixedRelaxedBlock3Step`) sourcing it from the base frame — so the
  residual does NOT carry a separate look-ahead cell for it.  The `lookahead`
  parameter is retained (unused) only to keep the consuming call sites stable.

  This file provides the definition together with the reload-boundary split
  identities `..._succ_zero` / `..._succ_one` and the empty-tail fact
  `..._ge_two`, which the induction uses to re-partition the residual at a
  reload before applying the IH.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadReshuffle

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Exponent residual for block `b` at pointer `ptr`: the not-yet-loaded limb
    cells strictly below `x16 = ptr`.  Counts are `2 / 1 / 0 / 0` by block; the
    cell addresses descend by `-8`.  (`lookahead` is unused — retained for call
    site stability; block 3's over-walk cell is base `a3`, handled by the
    relaxed block-3 engine, not the residual.) -/
@[irreducible]
def expTwoMulFixedExpResidual (b : Nat) (ptr _lookahead : Word)
    (exponentWord : EvmWord) : Assertion :=
  match b with
  | 0 =>
    (((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
        exponentWord.getLimbN 1) **
    ((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) +
        signExtend12 (0 : BitVec 12)) ↦ₘ exponentWord.getLimbN 0)
  | 1 =>
    (((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
        exponentWord.getLimbN 0)
  | _ => empAssertion

theorem expTwoMulFixedExpResidual_zero_unfold
    {ptr lookahead : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpResidual 0 ptr lookahead exponentWord =
      ((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 1) **
       ((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ exponentWord.getLimbN 0)) := by
  delta expTwoMulFixedExpResidual
  rfl

theorem expTwoMulFixedExpResidual_one_unfold
    {ptr lookahead : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpResidual 1 ptr lookahead exponentWord =
      (((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 0) := by
  delta expTwoMulFixedExpResidual
  rfl

theorem expTwoMulFixedExpResidual_ge_two
    {b : Nat} {ptr lookahead : Word} {exponentWord : EvmWord} (hb : 2 ≤ b) :
    expTwoMulFixedExpResidual b ptr lookahead exponentWord = empAssertion := by
  delta expTwoMulFixedExpResidual
  match b, hb with
  | (n + 2), _ => rfl

theorem expTwoMulFixedExpResidual_pcFree
    {b : Nat} {ptr lookahead : Word} {exponentWord : EvmWord} :
    (expTwoMulFixedExpResidual b ptr lookahead exponentWord).pcFree := by
  match b with
  | 0 =>
    rw [expTwoMulFixedExpResidual_zero_unfold]; pcFree
  | 1 =>
    rw [expTwoMulFixedExpResidual_one_unfold]; pcFree
  | (n + 2) =>
    rw [expTwoMulFixedExpResidual_ge_two (by omega)]; pcFree

instance pcFreeInst_expTwoMulFixedExpResidual
    (b : Nat) (ptr lookahead : Word) (exponentWord : EvmWord) :
    Assertion.PCFree (expTwoMulFixedExpResidual b ptr lookahead exponentWord) :=
  ⟨expTwoMulFixedExpResidual_pcFree⟩

/-- Reload-boundary split at block 0: the block-0 residual is the top cell at
    `ptr-8` (carrying `getLimbN 1`, the next iteration's pointer-cell value)
    separating-conjoined with the block-1 residual at the advanced pointer
    `ptr-8`.  The induction consumes the top cell into the next `IterPre` via the
    reload assembler and continues with `ExpResidual 1 (ptr-8)`. -/
theorem expTwoMulFixedExpResidual_succ_zero
    {ptr lookahead : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpResidual 0 ptr lookahead exponentWord =
      ((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 1) **
       expTwoMulFixedExpResidual 1 (ptr + signExtend12 (-8 : BitVec 12))
         lookahead exponentWord) := by
  rw [expTwoMulFixedExpResidual_zero_unfold,
    expTwoMulFixedExpResidual_one_unfold]

/-- Reload-boundary split at block 1: the single top cell at `ptr-8`
    (`getLimbN 0`) conjoined with the empty block-2 residual. -/
theorem expTwoMulFixedExpResidual_succ_one
    {ptr lookahead : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpResidual 1 ptr lookahead exponentWord =
      ((((ptr + signExtend12 (-8 : BitVec 12)) + signExtend12 (0 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 0) **
       expTwoMulFixedExpResidual 2 (ptr + signExtend12 (-8 : BitVec 12))
         lookahead exponentWord) := by
  rw [expTwoMulFixedExpResidual_one_unfold,
    expTwoMulFixedExpResidual_ge_two (b := 2) (by omega),
    sepConj_emp_right']

end EvmAsm.Evm64.Exp.Compose
