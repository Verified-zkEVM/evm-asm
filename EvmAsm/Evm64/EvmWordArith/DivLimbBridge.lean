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

/-- A nonzero 64-bit word has positive toNat. -/
theorem word_toNat_pos_of_ne_zero {w : Word} (h : w ≠ 0) : w.toNat > 0 := by
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
-- EvmWord nonzero ↔ getLimbN OR nonzero
-- ============================================================================

private theorem or_eq_zero_imp_left {a b : Word} (h : a ||| b = 0) : a = 0 := by
  bv_decide

private theorem or_eq_zero_imp_right {a b : Word} (h : a ||| b = 0) : b = 0 := by
  bv_decide

/-- An EvmWord is nonzero iff the OR of its four limbs is nonzero.
    Forward direction: needed to bridge `b ≠ 0` (EvmWord-level) to the
    limb-level `b0 ||| b1 ||| b2 ||| b3 ≠ 0` required by combined specs. -/
theorem ne_zero_iff_getLimbN_or (v : EvmWord) :
    v ≠ 0 ↔ v.getLimbN 0 ||| v.getLimbN 1 ||| v.getLimbN 2 ||| v.getLimbN 3 ≠ 0 := by
  constructor
  · -- → : v ≠ 0 implies OR of limbs ≠ 0 (contrapositive: OR = 0 → v = 0)
    intro hv hor
    apply hv
    -- OR is left-associated: ((a ||| b) ||| c) ||| d = 0
    have h3 := or_eq_zero_imp_right hor
    have h012 := or_eq_zero_imp_left hor
    have h2 := or_eq_zero_imp_right h012
    have h01 := or_eq_zero_imp_left h012
    have h1 := or_eq_zero_imp_right h01
    have h0 := or_eq_zero_imp_left h01
    -- All limbs 0 → v.toNat = 0 → v = 0
    have hd := toNat_getLimb_decompose v
    rw [getLimb_eq_getLimbN, getLimb_eq_getLimbN, getLimb_eq_getLimbN, getLimb_eq_getLimbN,
        fin4_val_0, fin4_val_1,
        fin4_val_2, fin4_val_3,
        h0, h1, h2, h3] at hd
    -- hd : v.toNat = 0 + 0 * 2^64 + 0 * 2^128 + 0 * 2^192
    simp at hd
    exact BitVec.eq_of_toNat_eq hd
  · -- ← : OR of limbs ≠ 0 implies v ≠ 0
    intro hor hv
    subst hv
    simp [getLimbN, getLimb] at hor

-- ============================================================================
-- fromLimbs reconstruction: individual Word values → EvmWord with known limbs
-- ============================================================================

/-- Construct an EvmWord from 4 Words via fromLimbs, with getLimbN round-trip.
    This is the key bridge for folding individual `↦ₘ` assertions back into
    `evmWordIs` in stack-level spec postconditions. -/
theorem getLimbN_fromLimbs_match {w0 w1 w2 w3 : Word} :
    let result := fromLimbs fun i : Fin 4 =>
      match i with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3
    result.getLimbN 0 = w0 ∧ result.getLimbN 1 = w1 ∧
    result.getLimbN 2 = w2 ∧ result.getLimbN 3 = w3 := by
  intro result
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [result, getLimbN, show (0 : Nat) < 4 from by omega,
               show (1 : Nat) < 4 from by omega,
               show (2 : Nat) < 4 from by omega,
               show (3 : Nat) < 4 from by omega, dite_true]
    exact getLimb_fromLimbs _ _

/-- Variant: the getLimbN of fromLimbs equals the corresponding input word.
    Useful for rewriting individual limb assertions. -/
theorem getLimbN_fromLimbs_0 {w0 w1 w2 w3 : Word} :
    (fromLimbs fun i : Fin 4 =>
      match i with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3).getLimbN 0 = w0 :=
  getLimbN_fromLimbs_match.1

theorem getLimbN_fromLimbs_1 {w0 w1 w2 w3 : Word} :
    (fromLimbs fun i : Fin 4 =>
      match i with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3).getLimbN 1 = w1 :=
  getLimbN_fromLimbs_match.2.1

theorem getLimbN_fromLimbs_2 {w0 w1 w2 w3 : Word} :
    (fromLimbs fun i : Fin 4 =>
      match i with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3).getLimbN 2 = w2 :=
  getLimbN_fromLimbs_match.2.2.1

theorem getLimbN_fromLimbs_3 {w0 w1 w2 w3 : Word} :
    (fromLimbs fun i : Fin 4 =>
      match i with | 0 => w0 | 1 => w1 | 2 => w2 | 3 => w3).getLimbN 3 = w3 :=
  getLimbN_fromLimbs_match.2.2.2

end EvmWord

end EvmAsm.Evm64
