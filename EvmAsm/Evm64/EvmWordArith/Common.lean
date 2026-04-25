/-
  EvmAsm.Evm64.EvmWordArith.Common

  Shared helpers for limb-level EvmWord correctness proofs.
-/

import EvmAsm.Evm64.Basic
import Mathlib.Tactic.Linarith

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- Shared helpers
-- ============================================================================

theorem bv_or_eq_zero {n : Nat} {x y : BitVec n} (h : x ||| y = 0) :
    x = 0 ∧ y = 0 :=
  BitVec.or_eq_zero_iff.mp h

theorem ult_one_eq_zero {x : Word} : BitVec.ult x 1 ↔ x = 0 := by
  constructor
  · intro h
    have h1 := of_decide_eq_true h
    change x.toNat < (1 : Word).toNat at h1
    apply BitVec.eq_of_toNat_eq
    have : (1 : Word).toNat = 1 := by decide
    have : (0 : Word).toNat = 0 := by decide
    omega
  · intro h; subst h; decide

theorem xor_eq_zero_imp {n : Nat} {x y : BitVec n} (h : x ^^^ y = 0) : x = y :=
  BitVec.xor_eq_zero_iff.mp h

-- OR of two borrow/carry flags (0-or-1 valued bitvectors)
theorem borrow_or_iff {c1 c2 : Prop} [Decidable c1] [Decidable c2] :
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)) =
    (if (c1 ∨ c2) then (1 : Word) else 0) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp_all

-- The toNat decomposition of a 256-bit value into 4 limbs.
theorem toNat_eq_limb_sum (v : EvmWord) :
    v.toNat = (v.getLimb 0).toNat + (v.getLimb 1).toNat * 2^64 +
              (v.getLimb 2).toNat * 2^128 + (v.getLimb 3).toNat * 2^192 := by
  simp only [getLimb, BitVec.extractLsb'_toNat,
    fin4_val_0, fin4_val_1, fin4_val_2, fin4_val_3,
    Nat.zero_mul, Nat.shiftRight_zero]
  have := v.isLt  -- v.toNat < 2^256
  omega

-- BitVec.ult ↔ toNat comparison
theorem ult_iff {n : Nat} {x y : BitVec n} : BitVec.ult x y ↔ x.toNat < y.toNat :=
  ⟨fun h => BitVec.lt_def.mp (of_decide_eq_true h),
   fun h => decide_eq_true (BitVec.lt_def.mpr h)⟩

-- Single-step borrow lemma: borrow condition ↔ multi-limb comparison.
-- M is the positional multiplier (2^64 at step 1, 2^128 at step 2, 2^192 at step 3).
-- aH, bH are single limbs (< 2^64). aLo, bLo are partial sums (< M).
theorem borrow_step_iff (M : Nat)
    {aH bH : Nat} (haH : aH < 2^64) (hbH : bH < 2^64)
    {aLo bLo : Nat} (haLo : aLo < M) (hbLo : bLo < M) :
    (aH < bH ∨ (aH + 2^64 - bH) % 2^64 < (if aLo < bLo then 1 else 0)) ↔
    (aLo + aH * M < bLo + bH * M) := by
  constructor
  · intro h; rcases h with h1 | h2
    · nlinarith [Nat.mul_le_mul_right M (show aH + 1 ≤ bH by omega)]
    · split at h2
      · have : (aH + 2^64 - bH) % 2^64 = 0 := by omega
        have : aH + 2^64 - bH < 2 * 2^64 := by omega
        have heq : aH = bH := by omega
        subst heq; omega
      · omega
  · intro h
    by_cases hcmp : aH < bH
    · left; exact hcmp
    · right
      have heq : aH = bH := by
        nlinarith [Nat.mul_le_mul_right M (show bH + 1 ≤ aH + 1 by omega)]
      subst heq
      have hlt : aLo < bLo := by omega
      simp [hlt]

/-- Helper: borrow flag value is 0 or 1. -/
theorem borrow_val_01 {c : Prop} [Decidable c] :
    (if c then (1 : Word) else (0 : Word)).toNat = 0 ∨
    (if c then (1 : Word) else (0 : Word)).toNat = 1 := by
  by_cases h : c <;> simp [h]

/-- Helper: OR of two borrow flags is 0 or 1. -/
theorem borrow_or_val_01 {c1 c2 : Prop} [Decidable c1] [Decidable c2] :
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)).toNat = 0 ∨
    ((if c1 then (1 : Word) else 0) ||| (if c2 then (1 : Word) else 0)).toNat = 1 := by
  rw [borrow_or_iff]
  exact borrow_val_01

end EvmWord

end EvmAsm.Evm64
