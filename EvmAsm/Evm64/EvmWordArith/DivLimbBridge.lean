/-
  EvmAsm.Evm64.EvmWordArith.DivLimbBridge

  Lemmas connecting limb-level properties (OR-reduce, val256 bounds)
  to EvmWord-level properties needed for division correctness.

  Key connections:
  - OR-reduce nonzero → at least one limb nonzero
  - Per-limb nonzero → val256 lower bound (per n-case)
  - OR-reduce nonzero → fromLimbs ≠ 0
  - val256-level Euclidean → EvmWord.div/mod correctness from limbs
-/

import EvmAsm.Evm64.EvmWordArith.DivBridge

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- OR-reduce nonzero → individual limb nonzero
-- ============================================================================

/-- If the 4-way OR of limbs is nonzero, at least one limb is nonzero. -/
theorem limbs_or_ne_zero_imp (b0 b1 b2 b3 : Word)
    (h : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    b0 ≠ 0 ∨ b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨h0, h1, h2, h3⟩ := hall
  exact h (by subst h0; subst h1; subst h2; subst h3; rfl)

-- ============================================================================
-- Word nonzero → toNat positive
-- ============================================================================

/-- A nonzero 64-bit word has toNat ≥ 1. -/
theorem word_toNat_pos_of_ne_zero {w : Word} (h : w ≠ 0) : w.toNat ≥ 1 := by
  by_contra hc; push Not at hc
  exact h (BitVec.eq_of_toNat_eq (by simp; omega))

-- ============================================================================
-- Per-limb nonzero → val256 lower bounds
-- ============================================================================

/-- If the lowest limb is nonzero, val256 ≥ 1. -/
theorem val256_pos_of_limb0 (b0 b1 b2 b3 : Word) (h : b0 ≠ 0) :
    val256 b0 b1 b2 b3 ≥ 1 := by
  unfold val256; have := word_toNat_pos_of_ne_zero h; nlinarith

/-- If limb 1 is nonzero, val256 ≥ 2^64. (n=2 case: divisor uses limbs 0–1.) -/
theorem val256_ge_pow64_of_limb1 (b0 b1 b2 b3 : Word) (h : b1 ≠ 0) :
    val256 b0 b1 b2 b3 ≥ 2^64 := by
  unfold val256; have := word_toNat_pos_of_ne_zero h; nlinarith

/-- If limb 2 is nonzero, val256 ≥ 2^128. (n=3 case: divisor uses limbs 0–2.) -/
theorem val256_ge_pow128_of_limb2 (b0 b1 b2 b3 : Word) (h : b2 ≠ 0) :
    val256 b0 b1 b2 b3 ≥ 2^128 := by
  unfold val256; have := word_toNat_pos_of_ne_zero h; nlinarith

/-- If limb 3 is nonzero, val256 ≥ 2^192. (n=4 case: divisor uses all limbs.) -/
theorem val256_ge_pow192_of_limb3 (b0 b1 b2 b3 : Word) (h : b3 ≠ 0) :
    val256 b0 b1 b2 b3 ≥ 2^192 := by
  unfold val256; have := word_toNat_pos_of_ne_zero h; nlinarith

-- ============================================================================
-- OR-reduce → val256/fromLimbs properties
-- ============================================================================

/-- OR-reduce nonzero implies val256 > 0. -/
theorem val256_pos_of_or_ne_zero (b0 b1 b2 b3 : Word)
    (h : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    val256 b0 b1 b2 b3 > 0 := by
  rcases limbs_or_ne_zero_imp b0 b1 b2 b3 h with h0 | h1 | h2 | h3
  · linarith [val256_pos_of_limb0 b0 b1 b2 b3 h0]
  · linarith [val256_ge_pow64_of_limb1 b0 b1 b2 b3 h1]
  · linarith [val256_ge_pow128_of_limb2 b0 b1 b2 b3 h2]
  · linarith [val256_ge_pow192_of_limb3 b0 b1 b2 b3 h3]

/-- OR-reduce nonzero implies the fromLimbs word is nonzero. -/
theorem fromLimbs_ne_zero_of_or (b0 b1 b2 b3 : Word)
    (h : b0 ||| b1 ||| b2 ||| b3 ≠ 0) :
    (fromLimbs fun i : Fin 4 =>
      match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) ≠ 0 := by
  intro heq
  have h0 : val256 b0 b1 b2 b3 = 0 := by
    rw [val256_eq_fromLimbs_toNat]
    have := congr_arg BitVec.toNat heq; simpa using this
  linarith [val256_pos_of_or_ne_zero b0 b1 b2 b3 h]

-- ============================================================================
-- Limb-level Euclidean → EvmWord.div/mod from limbs
-- ============================================================================

/-- Master bridge from limb-level Euclidean property to EvmWord.div.
    Given limb decompositions of a and b, and a Nat-level Euclidean
    equation in terms of val256, derives the EvmWord quotient. -/
theorem div_of_val256_euclidean (a b q r : EvmWord)
    (hbnz : b ≠ 0)
    (h_eq : a.toNat = b.toNat * q.toNat + r.toNat)
    (h_lt : r.toNat < b.toNat) :
    q = EvmWord.div a b :=
  div_of_nat_euclidean a b q r hbnz h_eq h_lt

/-- Master bridge from limb-level Euclidean property to EvmWord.mod. -/
theorem mod_of_val256_euclidean (a b q r : EvmWord)
    (hbnz : b ≠ 0)
    (h_eq : a.toNat = b.toNat * q.toNat + r.toNat)
    (h_lt : r.toNat < b.toNat) :
    r = EvmWord.mod a b :=
  mod_of_nat_euclidean a b q r hbnz h_eq h_lt

end EvmWord

end EvmAsm.Evm64
