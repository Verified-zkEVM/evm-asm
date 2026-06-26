/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedReloadReshuffle

  The reload-boundary pointer reshuffle for the fixed-x19 EXP loop.

  At a 64-bit limb boundary the loop body has already executed the reload
  (`LD x19 ← [x16]; ADDI x16 x16 -8`), so the loop-back post carries
  `expTwoMulFixedIterReloadPointerFrame ptr nextLimb = (x16 ↦ ptr-8) **
  (ptr ↦ nextLimb)`: the pointer register `x16` has advanced to `ptr-8`,
  but the live memory cell is still at the now-stale address `ptr`.

  The next iteration's `expTwoMulFixedIterPointerFrame (ptr-8) nextNextLimb`
  instead needs the cell at the *new* pointer `ptr-8`.  That cell is the next
  exponent limb, which lives in the induction residual `R` (the entry residual
  `expTwoMulFixedFirstIterEntryResidual` stages exactly the not-yet-loaded
  lower limbs).  So the reshuffle is a *pure* separation-logic re-partition:
  pull the `ptr-8` cell out of `R` into the pointer frame and push the stale
  `ptr` cell back into `R`.  No code step is required — the reload instructions
  already ran inside the finished iteration body.

  This lemma isolates that re-partition at the pointer-frame level; the
  256-iteration merged loop induction threads the exponent residual `R` so the
  `ptr-8` cell is in scope at each of the three limb boundaries.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCasePostFramedCases

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Reload-boundary pointer reshuffle (pure re-partition).

    Given the post-reload pointer frame `(x16 ↦ ptr-8) ** (ptr ↦ nextLimb)`
    together with the next-limb cell at `ptr-8` (supplied from the induction
    residual), regroup into the next iteration's pointer frame
    `(x16 ↦ ptr-8) ** (ptr-8 ↦ nextNextLimb)` plus the stale `ptr` cell
    (returned to the residual).  This is the entire content of the reload
    transition once the residual cell is in scope: a `sep_perm`. -/
theorem expTwoMulFixedIterReloadPointerFrame_reshuffle_to_pointerFrame
    {ptr nextLimb nextNextLimb : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    (expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  rw [expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

/-- The reverse re-partition: the next pointer frame plus the stale `ptr` cell
    regroup back into the post-reload reload-pointer frame plus the `ptr-8`
    cell.  Records that the reshuffle is an honest bijection on the heap
    (no cell is created or destroyed), useful when threading the residual in
    either direction. -/
theorem expTwoMulFixedIterPointerFrame_reshuffle_to_reloadPointerFrame
    {ptr nextLimb nextNextLimb : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
          nextNextLimb **
        ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps) :
    (expTwoMulFixedIterReloadPointerFrame ptr nextLimb **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps := by
  rw [expTwoMulFixedIterPointerFrame_unfold] at h
  rw [expTwoMulFixedIterReloadPointerFrame_unfold]
  sep_perm h

end EvmAsm.Evm64.Exp.Compose
