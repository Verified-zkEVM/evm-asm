/-
  EvmAsm.Evm64.Exp.Compose.SavedBitFixedIterCount

  Loop-counter invariant for the fixed x19 two-MUL saved-bit EXP induction.
-/

import EvmAsm.Evm64.Exp.Compose.SavedBitFixedLoopInvariant

namespace EvmAsm.Evm64.Exp.Compose

open EvmAsm.Rv64

/-- Expected remaining fixed-loop iterations at the start of semantic
    iteration `k`. -/
def expTwoMulFixedRemainingIterations (k : Nat) : Nat :=
  256 - k

/-- Machine loop-counter invariant for the fixed 256-iteration EXP loop. -/
def expTwoMulFixedIterCountInvariant (k : Nat) (iterCount : Word) : Prop :=
  iterCount.toNat = expTwoMulFixedRemainingIterations k

theorem expTwoMulFixedRemainingIterations_zero :
    expTwoMulFixedRemainingIterations 0 = 256 := by
  rfl

theorem expTwoMulFixedRemainingIterations_succ
    {k : Nat} (hk : k < 256) :
    expTwoMulFixedRemainingIterations (k + 1) + 1 =
      expTwoMulFixedRemainingIterations k := by
  unfold expTwoMulFixedRemainingIterations
  omega

theorem expTwoMulFixedRemainingIterations_succ_pos
    {k : Nat} (hk : k + 1 < 256) :
    0 < expTwoMulFixedRemainingIterations (k + 1) := by
  unfold expTwoMulFixedRemainingIterations
  omega

theorem expTwoMulFixedRemainingIterations_pos
    {k : Nat} (hk : k < 256) :
    0 < expTwoMulFixedRemainingIterations k := by
  unfold expTwoMulFixedRemainingIterations
  omega

theorem expTwoMulFixedRemainingIterations_succ_final :
    expTwoMulFixedRemainingIterations (255 + 1) = 0 := by
  rfl

/-- Block-bound at a non-final reload: a reload loop-back fires at a 64-bit
    boundary (`k % 64 = 63`) and, when it is not the loop exit (`k < 255`),
    the limb block index `k / 64` is strictly below 3.  This is the arithmetic
    core of the `ExpResidual` block-bound used by the residual-threaded merged
    induction: the look-ahead exponent cell is present (`ExpResidual` non-empty)
    at every reload, because the only `k / 64 = 3` reload coincides with the
    exit (`k = 255`), not a loop-back. -/
theorem expTwoMulFixedReloadBlock_lt_three
    {k : Nat} (hMod : k % 64 = 63) (hLt : k < 255) :
    k / 64 < 3 := by
  omega

/-- The non-final reload block index is exactly one of `0, 1, 2`. -/
theorem expTwoMulFixedReloadBlock_cases
    {k : Nat} (hMod : k % 64 = 63) (hLt : k < 255) :
    k / 64 = 0 ∨ k / 64 = 1 ∨ k / 64 = 2 := by
  omega

theorem expTwoMulFixedIterCountInvariant_zero :
    expTwoMulFixedIterCountInvariant 0 (256 : Word) := by
  unfold expTwoMulFixedIterCountInvariant
  simp [expTwoMulFixedRemainingIterations]

private theorem signExtend12_neg1_toNat :
    (signExtend12 (-1 : BitVec 12)).toNat = 2^64 - 1 := by
  decide

theorem expTwoMulIterCountNew_toNat_of_eq_succ
    {iterCount : Word} {n : Nat}
    (hCount : iterCount.toNat = n + 1) :
    (expTwoMulIterCountNew iterCount).toNat = n := by
  simp only [expTwoMulIterCountNew]
  rw [BitVec.toNat_add, signExtend12_neg1_toNat, hCount]
  have h_lt : n + 1 < 2^64 := by
    rw [← hCount]
    exact iterCount.isLt
  omega

theorem expTwoMulIterCountNew_ne_zero_of_toNat_succ_pos
    {iterCount : Word} {n : Nat}
    (hCount : iterCount.toNat = n + 1) (h_pos : 0 < n) :
    expTwoMulIterCountNew iterCount ≠ 0 := by
  intro h_zero
  have h_toNat : (expTwoMulIterCountNew iterCount).toNat = 0 := by
    simp [h_zero]
  rw [expTwoMulIterCountNew_toNat_of_eq_succ hCount] at h_toNat
  omega

theorem expTwoMulIterCountNew_eq_zero_of_toNat_one
    {iterCount : Word} (hCount : iterCount.toNat = 1) :
    expTwoMulIterCountNew iterCount = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp [expTwoMulIterCountNew_toNat_of_eq_succ
    (show iterCount.toNat = 0 + 1 from by omega)]

theorem expTwoMulFixedIterCountInvariant_succ
    {k : Nat} {iterCount : Word}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
    expTwoMulFixedIterCountInvariant (k + 1)
      (expTwoMulIterCountNew iterCount) := by
  unfold expTwoMulFixedIterCountInvariant at *
  have h_succ :
      iterCount.toNat =
        expTwoMulFixedRemainingIterations (k + 1) + 1 := by
    rw [hCount, expTwoMulFixedRemainingIterations_succ hk]
  exact expTwoMulIterCountNew_toNat_of_eq_succ h_succ

theorem expTwoMulFixedIterCountInvariant_ne_zero
    {k : Nat} {iterCount : Word}
    (hk : k < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
    iterCount ≠ 0 := by
  intro h_zero
  unfold expTwoMulFixedIterCountInvariant at hCount
  have h_toNat : iterCount.toNat = 0 := by
    simp [h_zero]
  rw [hCount] at h_toNat
  have h_pos := expTwoMulFixedRemainingIterations_pos hk
  omega

theorem expTwoMulFixedIterCountInvariant_succ_ne_zero
    {k : Nat} {iterCount : Word}
    (hk : k + 1 < 256)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
    expTwoMulIterCountNew iterCount ≠ 0 := by
  unfold expTwoMulFixedIterCountInvariant at hCount
  have hk_lt : k < 256 := by omega
  have h_succ :
      iterCount.toNat =
        expTwoMulFixedRemainingIterations (k + 1) + 1 := by
    rw [hCount, expTwoMulFixedRemainingIterations_succ hk_lt]
  exact expTwoMulIterCountNew_ne_zero_of_toNat_succ_pos h_succ
    (expTwoMulFixedRemainingIterations_succ_pos hk)

theorem expTwoMulFixedIterCountInvariant_succ_ne_zero_of_lt_255
    {k : Nat} {iterCount : Word}
    (hk : k < 255)
    (hCount : expTwoMulFixedIterCountInvariant k iterCount) :
    expTwoMulIterCountNew iterCount ≠ 0 := by
  exact expTwoMulFixedIterCountInvariant_succ_ne_zero (by omega) hCount

theorem expTwoMulFixedIterCountInvariant_succ_eq_zero
    {iterCount : Word}
    (hCount : expTwoMulFixedIterCountInvariant 255 iterCount) :
    expTwoMulIterCountNew iterCount = 0 := by
  unfold expTwoMulFixedIterCountInvariant at hCount
  have h_one : iterCount.toNat = 1 := by
    simpa [expTwoMulFixedRemainingIterations] using hCount
  exact expTwoMulIterCountNew_eq_zero_of_toNat_one h_one

@[irreducible]
def expTwoMulFixedIterCountAssertion
    (k : Nat) (iterCount : Word) : Assertion :=
  ⌜expTwoMulFixedIterCountInvariant k iterCount⌝

theorem expTwoMulFixedIterCountAssertion_unfold
    {k : Nat} {iterCount : Word} :
    expTwoMulFixedIterCountAssertion k iterCount =
      ⌜expTwoMulFixedIterCountInvariant k iterCount⌝ := by
  delta expTwoMulFixedIterCountAssertion
  rfl

theorem expTwoMulFixedIterCountAssertion_pcFree
    {k : Nat} {iterCount : Word} :
    (expTwoMulFixedIterCountAssertion k iterCount).pcFree := by
  rw [expTwoMulFixedIterCountAssertion_unfold]
  pcFree

instance pcFreeInst_expTwoMulFixedIterCountAssertion
    (k : Nat) (iterCount : Word) :
    Assertion.PCFree
      (expTwoMulFixedIterCountAssertion k iterCount) :=
  ⟨expTwoMulFixedIterCountAssertion_pcFree⟩

end EvmAsm.Evm64.Exp.Compose
