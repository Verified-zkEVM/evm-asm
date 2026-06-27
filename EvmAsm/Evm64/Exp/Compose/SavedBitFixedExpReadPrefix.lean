/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpReadPrefix

  The exponent *read prefix* `ExpReadPrefix` carried (as a framed pcFree
  assertion) by the merged-loop induction alongside `ExpResidual`.

  `ExpResidual b` tracks the exponent cells strictly *below* the loop pointer
  `x16 = ptr` that the loop has not yet loaded.  Dually, `ExpReadPrefix b`
  tracks the exponent cells strictly *above* `ptr` that the loop has *already*
  loaded (in earlier blocks) and that would otherwise drop anonymously into the
  read-only ambient frame at each reload.

  The full exponent operand lives in the four doublewords
  `evmSp-32 .. evmSp-8` (`= OUTER+32 .. OUTER+56`, little-endian limbs
  `getLimbN 0 .. getLimbN 3`).  By block `b` the top `b+1` of those have been
  read:

  * block 0 (`x16 = evmSp-16`): `evmSp-8` (`getLimbN 3`) — read by the prologue.
  * block 1 (`x16 = evmSp-24`): `+ evmSp-16` (`getLimbN 2`).
  * block 2 (`x16 = evmSp-32`): `+ evmSp-24` (`getLimbN 1`).
  * block 3 (`x16 = evmSp-40`, base `a3`): all four — the *full* operand
    `evmWordIs (evmSp-32) exponentWord`.

  At each reload the old pointer cell (the just-read limb) is absorbed into the
  prefix (`_succ_*` lemmas), so at the block-2→3 hand-off the prefix has grown
  to the complete `evmWordIs`, which the relaxed block-3 exit bridge consumes
  to reconstruct the `FullStackPreFrame` stack image.

  Addresses are written `(evmSp + signExtend12 (-32)) + k` to align with
  `evmWordIs`'s `addr / addr+8 / addr+16 / addr+24` layout, making
  `_three_eq_evmWordIs` definitional.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedExpResidual
import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64
open EvmAsm.Evm64

/-- Exponent read prefix for block `b`: the already-loaded exponent limb cells
    strictly above `x16`, aligned to the `evmWordIs (evmSp-32)` layout.  Counts
    are `1 / 2 / 3 / 4` by block; block `≥ 3` is the full operand. -/
@[irreducible]
def expTwoMulFixedExpReadPrefix (b : Nat) (evmSp : Word)
    (exponentWord : EvmWord) : Assertion :=
  let A : Word := evmSp + signExtend12 (-32 : BitVec 12)
  match b with
  | 0 =>
    ((A + 24) ↦ₘ exponentWord.getLimbN 3)
  | 1 =>
    ((A + 16) ↦ₘ exponentWord.getLimbN 2) **
    ((A + 24) ↦ₘ exponentWord.getLimbN 3)
  | 2 =>
    ((A + 8) ↦ₘ exponentWord.getLimbN 1) **
    ((A + 16) ↦ₘ exponentWord.getLimbN 2) **
    ((A + 24) ↦ₘ exponentWord.getLimbN 3)
  | _ =>
    (A ↦ₘ exponentWord.getLimbN 0) **
    ((A + 8) ↦ₘ exponentWord.getLimbN 1) **
    ((A + 16) ↦ₘ exponentWord.getLimbN 2) **
    ((A + 24) ↦ₘ exponentWord.getLimbN 3)

theorem expTwoMulFixedExpReadPrefix_zero_unfold
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 0 evmSp exponentWord =
      (((evmSp + signExtend12 (-32 : BitVec 12)) + 24) ↦ₘ
        exponentWord.getLimbN 3) := by
  delta expTwoMulFixedExpReadPrefix; rfl

theorem expTwoMulFixedExpReadPrefix_one_unfold
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 1 evmSp exponentWord =
      ((((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
          exponentWord.getLimbN 2) **
       (((evmSp + signExtend12 (-32 : BitVec 12)) + 24) ↦ₘ
          exponentWord.getLimbN 3)) := by
  delta expTwoMulFixedExpReadPrefix; rfl

theorem expTwoMulFixedExpReadPrefix_two_unfold
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 2 evmSp exponentWord =
      ((((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
          exponentWord.getLimbN 1) **
       (((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
          exponentWord.getLimbN 2) **
       (((evmSp + signExtend12 (-32 : BitVec 12)) + 24) ↦ₘ
          exponentWord.getLimbN 3)) := by
  delta expTwoMulFixedExpReadPrefix; rfl

/-- Block `≥ 3`: the prefix is the complete exponent operand
    `evmWordIs (evmSp-32) exponentWord`. -/
theorem expTwoMulFixedExpReadPrefix_three_eq_evmWordIs
    {b : Nat} {evmSp : Word} {exponentWord : EvmWord} (hb : 3 ≤ b) :
    expTwoMulFixedExpReadPrefix b evmSp exponentWord =
      evmWordIs (evmSp + signExtend12 (-32 : BitVec 12)) exponentWord := by
  delta expTwoMulFixedExpReadPrefix
  unfold evmWordIs
  match b, hb with
  | (n + 3), _ => rfl

theorem expTwoMulFixedExpReadPrefix_pcFree
    {b : Nat} {evmSp : Word} {exponentWord : EvmWord} :
    (expTwoMulFixedExpReadPrefix b evmSp exponentWord).pcFree := by
  match b with
  | 0 => rw [expTwoMulFixedExpReadPrefix_zero_unfold]; pcFree
  | 1 => rw [expTwoMulFixedExpReadPrefix_one_unfold]; pcFree
  | 2 => rw [expTwoMulFixedExpReadPrefix_two_unfold]; pcFree
  | (n + 3) =>
    rw [expTwoMulFixedExpReadPrefix_three_eq_evmWordIs (by omega)]
    exact pcFree_evmWordIs

instance pcFreeInst_expTwoMulFixedExpReadPrefix
    (b : Nat) (evmSp : Word) (exponentWord : EvmWord) :
    Assertion.PCFree (expTwoMulFixedExpReadPrefix b evmSp exponentWord) :=
  ⟨expTwoMulFixedExpReadPrefix_pcFree⟩

/-- Absorb at the block-0→1 reload: the just-read block-0 pointer cell
    (`evmSp-16 = (evmSp-32)+16`, value `getLimbN 2`) joins the prefix. -/
theorem expTwoMulFixedExpReadPrefix_succ_zero
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 1 evmSp exponentWord =
      ((((evmSp + signExtend12 (-32 : BitVec 12)) + 16) ↦ₘ
          exponentWord.getLimbN 2) **
       expTwoMulFixedExpReadPrefix 0 evmSp exponentWord) := by
  rw [expTwoMulFixedExpReadPrefix_one_unfold,
    expTwoMulFixedExpReadPrefix_zero_unfold]

/-- Absorb at the block-1→2 reload: the just-read block-1 pointer cell
    (`evmSp-24 = (evmSp-32)+8`, value `getLimbN 1`) joins the prefix. -/
theorem expTwoMulFixedExpReadPrefix_succ_one
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 2 evmSp exponentWord =
      ((((evmSp + signExtend12 (-32 : BitVec 12)) + 8) ↦ₘ
          exponentWord.getLimbN 1) **
       expTwoMulFixedExpReadPrefix 1 evmSp exponentWord) := by
  rw [expTwoMulFixedExpReadPrefix_two_unfold,
    expTwoMulFixedExpReadPrefix_one_unfold]

/-- Absorb at the block-2→3 reload: the just-read block-2 pointer cell
    (`evmSp-32`, value `getLimbN 0`) joins the prefix, completing the full
    exponent operand `evmWordIs (evmSp-32) exponentWord`. -/
theorem expTwoMulFixedExpReadPrefix_succ_two
    {evmSp : Word} {exponentWord : EvmWord} :
    expTwoMulFixedExpReadPrefix 3 evmSp exponentWord =
      (((evmSp + signExtend12 (-32 : BitVec 12)) ↦ₘ
          exponentWord.getLimbN 0) **
       expTwoMulFixedExpReadPrefix 2 evmSp exponentWord) := by
  rw [expTwoMulFixedExpReadPrefix_three_eq_evmWordIs (by omega),
    expTwoMulFixedExpReadPrefix_two_unfold]
  unfold evmWordIs
  rfl

end EvmAsm.Evm64.Exp.Compose
