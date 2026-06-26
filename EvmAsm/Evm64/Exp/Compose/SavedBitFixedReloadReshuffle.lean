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

/-- Suffix-level reload reshuffle (conditional-multiply branch).

    Lifts the pointer-cell reshuffle to the full reload-cond scratch suffix
    frame that appears in the merged loop-back reload disjunct: given that
    suffix together with the next-limb cell at `ptr-8` (from the induction
    residual), regroup the `reloadPointerFrame` into the next iteration's
    `IterPointerFrame (ptr-8)` and return the stale `ptr` cell.  All other
    suffix atoms (the cursor `x19`, reset counter `x20`, saved bit `x18`, the
    `c6New = 0` / `bit ≠ 0` pures, the `SkipCondRestScratchSuffix`) are
    unchanged — this is a pure `sep_perm` once the pointer frames unfold. -/
theorem expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame_reshuffle
    {e c6 ptr nextLimb nextNextLimb base : Word} {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame
          e c6 ptr nextLimb base **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    (expTwoMulFixedIterSkipCondRestScratchSuffix base **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) ≠ 0⌝ **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  simp only [expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

/-- Suffix-level reload reshuffle (skip / no-conditional-multiply branch).
    The skip variant of
    `expTwoMulFixedIterReloadCondCountPostScratchSuffixFrame_reshuffle`: the
    suffix carries the `x1` return slot and the `IterBaseFrame` instead of the
    `SkipCondRestScratchSuffix`, and the `bit = 0` pure; the reshuffle is again
    a pure `sep_perm`. -/
theorem expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame_reshuffle
    {e c6 ptr nextLimb nextNextLimb evmSp a0 a1 a2 a3 base : Word}
    {ps : PartialState}
    (h :
      (expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame
          e c6 ptr nextLimb evmSp a0 a1 a2 a3 base **
        (((ptr + signExtend12 (-8 : BitVec 12)) +
          signExtend12 (0 : BitVec 12)) ↦ₘ nextNextLimb)) ps) :
    ((.x1 ↦ᵣ (((base + 44) + 32) + 68)) **
      (.x19 ↦ᵣ nextLimb) **
      (.x20 ↦ᵣ ((0 : Word) + signExtend12 (64 : BitVec 12))) **
      (.x18 ↦ᵣ ((e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12))) **
      ⌜c6 + signExtend12 (-1 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterPointerFrame (ptr + signExtend12 (-8 : BitVec 12))
        nextNextLimb **
      ⌜(e >>> (63 : BitVec 6).toNat) + signExtend12 (0 : BitVec 12) = 0⌝ **
      expTwoMulFixedIterBaseFrame evmSp a0 a1 a2 a3 **
      ((ptr + signExtend12 (0 : BitVec 12)) ↦ₘ nextLimb)) ps := by
  simp only [expTwoMulFixedIterReloadSkipCountPostScratchSuffixFrame,
    expTwoMulFixedIterReloadPointerFrame_unfold] at h
  rw [expTwoMulFixedIterPointerFrame_unfold]
  sep_perm h

end EvmAsm.Evm64.Exp.Compose
