/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

  Replacement for PR #1154 (closed). Proves the call-skip exact lower bound
  `val256(a)/val256(b) ≤ (div128Quot u4 u3 b3').toNat` under shift_nz + hcall,
  via a **GLOBAL Phase 1+2 compensation argument** instead of the per-phase
  tight bounds that PR #1154 attempted.

  Background (why per-phase fails): see
  `memory/project_knuth_b_lower_large_rhatc.md` and
  `memory/project_a2s2_per_phase_tightness_fails.md`. The overall Knuth bound
  `qHat ≥ q_true_full` holds only because Phase 2 compensates Phase 1
  undershoots — a global, not per-phase, property.

  ## Status (2026-04-25 — SORRY-FREE)

  **Top-level theorem `div128Quot_call_skip_ge_val256_div_v2` proven.**
  All sorries in CallSkipLowerBoundV2 are now closed.

  Phase 2 tightness for un21 ≥ 2^63 closes via the unconditional
  un21-level helper `div128Quot_q0_prime_ge_q_true_0_un21_level` in
  `CompensationCases.lean`, which uses the algorithm's own Phase 2b
  truncation guard to dispatch between `_small_rhatc` (when rhat2c <
  2^32) and KB-LB3 (when rhat2c ≥ 2^32).

  All wide-u4 sub-cases are CLOSED VACUOUSLY via the `hu4_lt_pow63`
  hypothesis (u4 < 2^63), threaded through from the top-level theorem
  where it's derived via `u_top_lt_pow63_of_shift_nz` +
  `clzResult_fst_toNat_le`. The "wide-u4 no-undershoot was FALSE"
  finding from `memory/project_wide_u4_no_undershoot_false_in_b2.md` is
  RESOLVED — the failing example is unreachable from the top-level call.

  ## File structure (5 modules)

  - `CallSkipLowerBoundV2/Algorithm.lean` — irreducible algorithm bundles
    (algorithmUn21, algorithmQ1Prime, algorithmQ0Prime).
  - `CallSkipLowerBoundV2/QuotientBounds.lean` — Q1Prime / Q0Prime bounds,
    `_plus_one` 6-step decomposition.
  - `CallSkipLowerBoundV2/Un21Bridge.lean` — Layer 1/2/3 helpers, _of_tight
    cases, algorithmUn21_ge_r1_math wrapper.
  - `CallSkipLowerBoundV2/CompensationCases.lean` — A2 normal +
    compensation cases + A4 normalized.
  - This file: §B (val256 bridge) and final composition.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.CompensationCases
import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity
import EvmAsm.Evm64.EvmWordArith.DivLimbBridge
import EvmAsm.Evm64.EvmWordArith.MultiLimb

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

-- Re-exported via the import chain:
-- `CallSkipLowerBoundV2/Algorithm.lean`         — irreducible algorithm bundles
-- `CallSkipLowerBoundV2/QuotientBounds.lean`     — Q1Prime / Q0Prime bounds + 6-step plus_one
-- `CallSkipLowerBoundV2/Un21Bridge.lean`         — Layer 1/2/3 + _of_tight + ge_r1_math
-- `CallSkipLowerBoundV2/CompensationCases.lean`  — A2 normal/compensation + A4 normalized
--
-- This file holds §B (val256 bridge) and the final composition
-- `div128Quot_call_skip_ge_val256_div_v2`.

-- =============================================================================
-- §B — Bridge from val256 to 128/64 (normalization)
-- =============================================================================

/-- **B3.1**: pure Nat truncation-division identity.
    `(A * K + L) / (B * K) = A / B` when `0 < K, 0 < B, L < K`.

    Proof: A = B*q + r with r < B. Then A*K + L = B*K*q + (r*K + L) with
    r*K + L < B*K. Apply Nat.add_mul_div_right / Nat.div_eq_of_lt_of_lt. -/
theorem nat_trunc_div_add_lt (A B K L : Nat)
    (hK_pos : 0 < K) (hB_pos : 0 < B) (hL_lt : L < K) :
    (A * K + L) / (B * K) = A / B := by
  have hBK_pos : 0 < B * K := Nat.mul_pos hB_pos hK_pos
  have hA_eq : A = B * (A / B) + A % B := (Nat.div_add_mod A B).symm
  have hr_lt : A % B < B := Nat.mod_lt A hB_pos
  have h_expand : A * K + L = (A / B) * (B * K) + ((A % B) * K + L) := by
    conv_lhs => rw [hA_eq]
    ring
  have h_rem_bound : (A % B) * K + L < B * K := by
    have h_rK : (A % B) * K ≤ (B - 1) * K := Nat.mul_le_mul_right _ (by omega)
    have h_step : (B - 1) * K + K = B * K := by
      have : B = (B - 1) + 1 := by omega
      conv_rhs => rw [this]
      ring
    omega
  rw [h_expand]
  rw [show A / B * (B * K) + (A % B * K + L) = (A % B * K + L) + B * K * (A / B) from by ring]
  rw [Nat.add_mul_div_left _ _ hBK_pos]
  rw [Nat.div_eq_of_lt h_rem_bound]
  omega

/-- **B3.2**: val256(b_norm) is at least b3' * 2^192.
    Trivial from val256 definition (b3' is the top limb, other limbs ≥ 0). -/
theorem val256_ge_top_limb_mul_pow192 (b0 b1 b2 b3 : Word) :
    val256 b0 b1 b2 b3 ≥ b3.toNat * 2^192 := by
  unfold val256; omega

/-- **B3.3**: decomposition of the normalized+overflow dividend.
    `val256(a_norm) + u4 * 2^256 = (u4*2^64 + u3) * 2^192 + lower` where
    `lower = val256(a_norm.getLimbN 0, 1, 2, 0) < 2^192` (bottom 3 limbs).
    The u3 is a_norm's top limb.

    Specialized form: takes the 4 normalized limbs explicitly. -/
theorem a_scaled_decomp (u_norm0 u_norm1 u_norm2 u3 u4 : Word) :
    val256 u_norm0 u_norm1 u_norm2 u3 + u4.toNat * 2^256 =
    (u4.toNat * 2^64 + u3.toNat) * 2^192 +
      (u_norm0.toNat + u_norm1.toNat * 2^64 + u_norm2.toNat * 2^128) := by
  unfold val256; ring

/-- The lower-3-limb val256 is bounded by 2^192 (since each limb < 2^64). -/
theorem val256_lower3_lt_pow192 (x0 x1 x2 : Word) :
    x0.toNat + x1.toNat * 2^64 + x2.toNat * 2^128 < 2^192 := by
  have h0 := x0.isLt
  have h1 := x1.isLt
  have h2 := x2.isLt
  calc x0.toNat + x1.toNat * 2^64 + x2.toNat * 2^128
      ≤ (2^64 - 1) + (2^64 - 1) * 2^64 + (2^64 - 1) * 2^128 := by
        have h1' : x1.toNat * 2^64 ≤ (2^64 - 1) * 2^64 :=
          Nat.mul_le_mul_right _ (by omega)
        have h2' : x2.toNat * 2^128 ≤ (2^64 - 1) * 2^128 :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    _ < 2^192 := by decide

/-- **B3.4** (the §B target-minus-one): val256 ratio bound via normalization.
    `val256(a) / val256(b) ≤ (u4*2^64 + u3) / b3'`.

    Proof: cancel 2^shift in LHS, apply normalization identities
    `u_val256_eq_scaled_with_overflow` + `b3_prime_val256_eq_scaled`,
    then use `Nat.div_le_div_left` + `a_scaled_decomp` + `nat_trunc_div_add_lt`. -/
theorem val256_ratio_le_u_total_div_b3_prime
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat := by
  simp only []
  -- Step 1: cancel 2^shift via Nat.mul_div_mul_right.
  have h_pow_pos : (0 : Nat) < 2^(clzResult b3).1.toNat := by positivity
  have h_cancel :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 =
      (val256 a0 a1 a2 a3 * 2^(clzResult b3).1.toNat) /
      (val256 b0 b1 b2 b3 * 2^(clzResult b3).1.toNat) :=
    (Nat.mul_div_mul_right _ _ h_pow_pos).symm
  rw [h_cancel]
  -- Step 2: rewrite numerator via `u_val256_eq_scaled_with_overflow`.
  have h_norm_u := u_val256_eq_scaled_with_overflow a0 a1 a2 a3 b3 hshift_nz
  -- Step 3: rewrite denominator via `b3_prime_val256_eq_scaled`.
  have h_norm_v := b3_prime_val256_eq_scaled b0 b1 b2 b3 hshift_nz
  rw [← h_norm_u, ← h_norm_v]
  -- Goal: (val256(a_norm) + u4*2^256) / val256(b_norm) ≤ (u4*2^64+u3)/b3'.
  set b3_prime := (b3 <<< ((clzResult b3).1.toNat % 64)) |||
    (b2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    with hb3_prime_def
  set u4 := a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)
    with hu4_def
  set u3 := (a3 <<< ((clzResult b3).1.toNat % 64)) |||
    (a2 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))
    with hu3_def
  -- Step 4: val256(b_norm) ≥ b3' * 2^192.
  have h_b_ge : (val256
    (b0 <<< ((clzResult b3).1.toNat % 64))
    ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
       (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
       (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
    b3_prime) ≥ b3_prime.toNat * 2^192 := val256_ge_top_limb_mul_pow192 _ _ _ _
  -- Step 5: b3' > 0 (to apply div_le_div_left).
  have hb3_prime_ge_pow63 : b3_prime.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hb3_prime_pos : 0 < b3_prime.toNat := by omega
  have hb3_prime_pow_pos : 0 < b3_prime.toNat * 2^192 := by
    have : (0 : Nat) < 2^192 := by positivity
    exact Nat.mul_pos hb3_prime_pos this
  -- Step 6: Nat.div_le_div_left with the ≥ relationship.
  have h_step1 :
      (val256
         (a0 <<< ((clzResult b3).1.toNat % 64))
         ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
            (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
            (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         u3 + u4.toNat * 2^256) /
        (val256
          (b0 <<< ((clzResult b3).1.toNat % 64))
          ((b1 <<< ((clzResult b3).1.toNat % 64)) |||
             (b0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
          ((b2 <<< ((clzResult b3).1.toNat % 64)) |||
             (b1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
          b3_prime) ≤
      (val256
         (a0 <<< ((clzResult b3).1.toNat % 64))
         ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
            (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
            (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64)))
         u3 + u4.toNat * 2^256) / (b3_prime.toNat * 2^192) :=
    Nat.div_le_div_left h_b_ge hb3_prime_pow_pos
  refine Nat.le_trans h_step1 ?_
  -- Step 7: use a_scaled_decomp + nat_trunc_div_add_lt.
  rw [a_scaled_decomp]
  -- Goal: ((u4*2^64+u3)*2^192 + lower) / (b3'*2^192) ≤ (u4*2^64+u3)/b3'.
  have h_lower_lt : (a0 <<< ((clzResult b3).1.toNat % 64)).toNat +
      ((a1 <<< ((clzResult b3).1.toNat % 64)) |||
         (a0 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat *
        2^64 +
      ((a2 <<< ((clzResult b3).1.toNat % 64)) |||
         (a1 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64))).toNat *
        2^128 < 2^192 := val256_lower3_lt_pow192 _ _ _
  have h_pow192_pos : (0 : Nat) < 2^192 := by positivity
  rw [nat_trunc_div_add_lt _ _ _ _ h_pow192_pos hb3_prime_pos h_lower_lt]

/-- **B4** (the §B target, wrapper form). -/
theorem q_true_triple_bridge_to_val256_norm
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hb3nz : b3 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat :=
  val256_ratio_le_u_total_div_b3_prime a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz

-- =============================================================================
-- Main theorem: composition
-- =============================================================================

/-- **Call-skip exact lower bound** (the target of PR #1154 replacement). -/
theorem div128Quot_call_skip_ge_val256_div_v2
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h_bridge
  have h_b3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have h_u4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  -- u4 < 2^63 derived from u4 = a3 >> antiShift with antiShift ≥ 1 (shift ≠ 0).
  -- Direct application of `u_top_lt_pow63_of_shift_nz` (MaxTrialVacuity.lean).
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso; apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have h_core := div128Quot_ge_q_true_normalized u4 u3 b3' h_b3'_ge h_u4_lt_b3' h_u4_lt_pow63
  exact Nat.le_trans h_bridge h_core

/-- **Tight equality `qHat = val256(a)/val256(b)` under skip-borrow** (CLOSED).

    Composes the upper bound (`div128Quot_call_skip_le_val256_div`
    from `Div128CallSkipClose`, needs `isSkipBorrowN4Call`) with the
    lower bound (`div128Quot_call_skip_ge_val256_div_v2`, this file,
    needs only the call-trial preconditions). Yields the EXACT
    equality:

    ```
    (div128Quot u4 un3 b3').toNat = val256(a)/val256(b)
    ```

    This is the "Knuth-D ideal" — the bare-trial `div128Quot`
    matches the true 256-bit quotient exactly when the outer mulsub
    doesn't borrow. All Knuth-B/C overshoot cases are excluded by
    skip-borrow.

    Building block for the discharge bridge: from this tight equality
    we derive q1' = q_true_1 (Phase 1 tight) and q0' < 2^32
    (Phase 2 sane), which together imply `Div128AllPhasesNoWrapInv`. -/
theorem div128Quot_call_skip_eq_val256_div
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    (div128Quot u4 un3 b3').toNat = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  intro shift antiShift u4 un3 b3'
  have h_le := div128Quot_call_skip_le_val256_div a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hborrow
  have h_ge := div128Quot_call_skip_ge_val256_div_v2 a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall
  simp only [] at h_le h_ge
  exact Nat.le_antisymm h_le h_ge

/-- **Bound `val256(a)/val256(b) < 2^64` under `b3 ≠ 0`** (CLOSED).

    The 256-bit true quotient fits in a Word. From `val256(a) < 2^256`
    and `val256(b) ≥ 2^192`, we get `val256(a)/val256(b) < 2^64`.

    Used downstream to:
    1. Show `div128Quot.toNat < 2^64` directly (always true, but here
       linked to q_true_full).
    2. Conclude `q_true_1 < 2^32` (high digit) for digit decomposition. -/
theorem val256_div_val256_lt_pow64 (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0) :
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 < 2^64 := by
  have h_a_lt : val256 a0 a1 a2 a3 < 2^256 := EvmWord.val256_bound _ _ _ _
  have h_b_ge : val256 b0 b1 b2 b3 ≥ 2^192 := EvmWord.val256_ge_pow192_of_limb3 _ _ _ _ hb3nz
  have h_b_pos : val256 b0 b1 b2 b3 > 0 := by
    have : (2^192 : Nat) > 0 := by decide
    omega
  have h192_pos : (0 : Nat) < 2^192 := by decide
  have h_div_le : val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      val256 a0 a1 a2 a3 / 2^192 :=
    Nat.div_le_div_left h_b_ge h192_pos
  have h_a_div : val256 a0 a1 a2 a3 / 2^192 < 2^64 := by
    have h_pow : (2^256 : Nat) = 2^192 * 2^64 := by decide
    have h192_pos : (2^192 : Nat) > 0 := by decide
    rw [Nat.div_lt_iff_lt_mul h192_pos]
    have : (2 ^ 192 * 2 ^ 64 : Nat) = 2 ^ 256 := by decide
    omega
  omega

/-- **Combined: q_true_1 < 2^32 and q_true_0 < 2^32** for the
    256-bit true quotient digit decomposition.

    Pure Nat consequence of `val256_div_val256_lt_pow64` and the
    standard mod-2^32 bound. Used to apply `digit_tight_of_le_and_ge`. -/
theorem val256_div_q_true_digits_lt_pow32
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (hb3nz : b3 ≠ 0) :
    let q_true_full := val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3
    q_true_full / 2^32 < 2^32 ∧ q_true_full % 2^32 < 2^32 := by
  intro q_true_full
  have h_full_lt : q_true_full < 2^64 :=
    val256_div_val256_lt_pow64 a0 a1 a2 a3 b0 b1 b2 b3 hb3nz
  refine ⟨?_, ?_⟩
  · -- q_true_full / 2^32 < 2^32: from q_true_full < 2^64.
    have h_pow : (2^64 : Nat) = 2^32 * 2^32 := by decide
    rw [Nat.div_lt_iff_lt_mul (by decide : (0:Nat) < 2^32)]
    omega
  · -- q_true_full % 2^32 < 2^32: standard.
    exact Nat.mod_lt _ (by decide)

/-- **OR-left lower bound**: `((q1' << 32) ||| q0').toNat ≥ q1'.toNat * 2^32`
    when `q1' < 2^32`.

    Pure BitVec property: `a OR b ≥ a` (bitwise), and the shift preserves
    the lower bits. Useful primitive for the digit-decomposition
    argument: combined with `qHat = q_true_full = q_true_1 * 2^32 + q_true_0`
    (under skip-borrow tight equality), gives `q1' * 2^32 ≤ qHat
    ≤ (q_true_1 + 1) * 2^32 - 1`, hence `q1' ≤ q_true_1`. -/
theorem div128Quot_or_left_ge_q1_prime_shift
    (q1' q0' : Word) (h_q1'_lt : q1'.toNat < 2^32) :
    q1'.toNat * 2^32 ≤ ((q1' <<< (32 : BitVec 6).toNat) ||| q0').toNat := by
  have h_or_ge : (q1' <<< (32 : BitVec 6).toNat).toNat ≤
      ((q1' <<< (32 : BitVec 6).toNat) ||| q0').toNat := by
    rw [BitVec.toNat_or]
    exact Nat.left_le_or
  have h_shift_eq : (q1' <<< (32 : BitVec 6).toNat).toNat = q1'.toNat * 2^32 := by
    rw [BitVec.toNat_shiftLeft]
    simp only [Nat.shiftLeft_eq, EvmAsm.Rv64.AddrNorm.bv6_toNat_32]
    have : q1'.toNat * 2^32 < 2^64 := by
      have : (2^64 : Nat) = 2^32 * 2^32 := by decide
      nlinarith
    rw [Nat.mod_eq_of_lt this]
  omega

/-- **Pure-Nat: from `q1 * 2^32 ≤ q_true_full`, derive `q1 ≤ q_true_full / 2^32`.**

    Stepping stone toward q1' ≤ q_true_top_at_val256_level. Pure Nat
    consequence of `Nat.le_div_iff_mul_le` (basically `q ≤ Y/v ⟺ q*v ≤ Y`). -/
theorem q1_le_q_true_top_of_mul_pow32_le
    (q1 q_true_full : Nat)
    (h_mul : q1 * 2^32 ≤ q_true_full) :
    q1 ≤ q_true_full / 2^32 :=
  (Nat.le_div_iff_mul_le (by decide : (0:Nat) < 2^32)).mpr h_mul

/-- **div128Quot OR-left bound, no q0' extraction** (CLOSED).

    Generic version: for ANY Word `qHat` viewed as `(q1 << 32) ||| q0` for
    some q0, `q1 * 2^32 ≤ qHat.toNat` provided `q1 < 2^32` AND there
    exists a Word q0 with `qHat = (q1 << 32) ||| q0`. Trivial — q0 is
    just `qHat AND ~(q1 << 32)` (or any Word; the OR-bound holds regardless).

    Used in the algorithm-level Phase 1 tight lemma below. -/
theorem div128Quot_or_left_ge_q1_prime_shift_existential
    (qHat q1 : Word) (q0 : Word)
    (h_eq : qHat = (q1 <<< (32 : BitVec 6).toNat) ||| q0)
    (h_q1_lt : q1.toNat < 2^32) :
    q1.toNat * 2^32 ≤ qHat.toNat := by
  rw [h_eq]
  exact div128Quot_or_left_ge_q1_prime_shift q1 q0 h_q1_lt

/-- **Algorithm-level Phase 1 tight upper bound under skip-borrow** (CLOSED).

    `q1' ≤ val256(a)/val256(b) / 2^32` — the algorithm's high-digit
    trial is at most the true 256-bit quotient's high digit, when
    skip-borrow holds.

    Composes:
    1. `div128Quot_call_skip_eq_val256_div`: tight equality
       `qHat.toNat = val256(a)/val256(b)`.
    2. `div128Quot_q1_prime_lt_pow32_call`: q1' < 2^32.
    3. `div128Quot_or_left_ge_q1_prime_shift_existential`: applied to
       div128Quot's OR-decomposition (by `rfl`).
    4. `q1_le_q_true_top_of_mul_pow32_le`: pure-Nat division step. -/
theorem div128Quot_q1_prime_le_q_true_top_call_skip
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    q1'.toNat ≤ (val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3) / 2^32 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1'
  have h_eq := div128Quot_call_skip_eq_val256_div a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall hborrow
  simp only [] at h_eq
  have h_q1'_lt := div128Quot_q1_prime_lt_pow32_call a2 a3 b2 b3 hb3nz hcall
  simp only [] at h_q1'_lt
  -- The OR-decomposition: div128Quot u4 un3 b3' = (q1' << 32) ||| q0'
  -- where q0' is whatever div128Quot's body computes. By definition.
  set q0_word : Word :=
    let div_un0 := (un3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let cu_rhat_un1 :=
      ((if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) <<<
        (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    div128Quot_phase2b_q0' q0c rhat2c dLo div_un0 with hq0_def
  have h_div_eq : div128Quot u4 un3 b3' =
      (q1' <<< (32 : BitVec 6).toNat) ||| q0_word := by
    rfl
  have h_or_ge : q1'.toNat * 2^32 ≤ (div128Quot u4 un3 b3').toNat :=
    div128Quot_or_left_ge_q1_prime_shift_existential
      (div128Quot u4 un3 b3') q1' q0_word h_div_eq h_q1'_lt
  have h_mul_le : q1'.toNat * 2^32 ≤ val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 :=
    h_or_ge.trans (le_of_eq h_eq)
  exact q1_le_q_true_top_of_mul_pow32_le _ _ h_mul_le

/-- **Multiplicative form** of `div128Quot_q1_prime_le_q_true_top_call_skip`:
    `q1' * 2^32 ≤ val256(a)/val256(b)` under skip-borrow.

    Direct restatement using `Nat.le_div_iff_mul_le.mpr`'s converse —
    avoids the `_ / 2^32` form when callers want the multiplicative
    inequality directly. -/
theorem div128Quot_q1_prime_mul_pow32_le_val256_div_call_skip
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3)
    (hborrow : isSkipBorrowN4Call a0 a1 a2 a3 b0 b1 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let u4 := a3 >>> antiShift
    let un3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := un3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    q1'.toNat * 2^32 ≤ val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
  intro shift antiShift u4 un3 b3' dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
        rhatUn1 q1'
  have h_div := div128Quot_q1_prime_le_q_true_top_call_skip a0 a1 a2 a3 b0 b1 b2 b3
    hb3nz hshift_nz hcall hborrow
  simp only [] at h_div
  -- h_div: q1'.toNat ≤ (val256 a / val256 b) / 2^32.
  -- Apply Nat.le_div_iff_mul_le.mp to get q1' * 2^32 ≤ val256/val256.
  exact (Nat.le_div_iff_mul_le (by decide : (0:Nat) < 2^32)).mp h_div

end EvmAsm.Evm64
