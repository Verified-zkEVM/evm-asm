/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD

  Shared declaration home for the V5 lower-bound proof chain.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainC
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.LowerBound

  **V5.5.3**: `q_true ≤ div128Quot_v5` unconditionally.

  Composition: V5.5.1 (Q1dd = q_true_1) + V5.4.3 (un21 = r1) +
  V5.5.2 (Q0dd ≥ q_true_0) via `div128_two_step_lower_of_q0_lower_nat`.

  Uses the same sorry bridge as V5.4.5 (divKTrialCallV5QHat_eq_div128Quot_v5).

  Bead evm-asm-wbc4i.5.3 (V5.5.3).
-/


namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- **V5.5.3**: `q_true ≤ div128Quot_v5` unconditionally. -/
theorem div128Quot_v5_ge_q_true
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (div128Quot_v5 uHi uLo vTop).toNat := by
  rw [← divKTrialCallV5QHat_eq_div128Quot_v5]
  let q1 := divKTrialCallV5Q1dd uHi uLo vTop
  let q0 := divKTrialCallV5Q0dd uHi uLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let un0 := divKTrialCallV5Un0 uLo
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  -- q1 = q_true_1 (pin)
  have hq1_eq : q1.toNat = (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_eq_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- q0 ≥ q_true_0
  have hq0_ge : (un21.toNat * 2^32 + un0.toNat) / vTop.toNat ≤ q0.toNat :=
    divKTrialCallV5Q0dd_ge_q_true_0 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- un21 = r1
  have h_un21_eq_r1 : un21.toNat = (uHi.toNat * 2^32 + un1.toNat) % vTop.toNat :=
    divKTrialCallV5Un21_eq_r1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Q1dd and Q0dd < 2^32
  have h_q1_lt : q1.toNat < 2^32 := by
    have h_N_lt : uHi.toNat * 2^32 + un1.toNat < vTop.toNat * 2^32 := by
      have := divKTrialCallV5Un1_lt_pow32 uLo; nlinarith
    have : (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  have h_q0_lt : q0.toNat < 2^32 := by
    exact lt_of_le_of_lt
      (show q0.toNat ≤ (divKTrialCallV5Q0c uHi uLo vTop).toNat from
        le_trans
          (show q0.toNat ≤ (divKTrialCallV5Q0d uHi uLo vTop).toNat from by
            show (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤ _
            delta divKTrialCallV5Q0dd; exact div128Quot_phase2b_q0'_le_self _ _ _ _)
          (by unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _))
      (by rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop)
  -- QHat.toNat = q1 * 2^32 + q0
  have h_qhat : (divKTrialCallV5QHat uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat := by
    unfold divKTrialCallV5QHat
    rw [show (32 : BitVec 6).toNat = 32 from by decide]
    exact EvmWord.halfword_combine _ _ h_q1_lt h_q0_lt
  rw [h_qhat]
  -- uLo = un1 * 2^32 + un0
  have h_uLo : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV5Un1 divKTrialCallV5Un0
    exact div128Quot_vTop_decomp uLo
  -- Two-step LB
  have h_core := div128_two_step_lower_of_q0_lower_nat
    uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat un21.toNat
    hvTop_pos hq1_eq h_un21_eq_r1 hq0_ge
  rw [show uHi.toNat * 2^64 + uLo.toNat = uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat from by
    rw [h_uLo]; ring]
  exact h_core

-- ============================================================================
-- div128Quot_v5 = floor  (exact 128/64 quotient — the n4 +2 enabler)
-- ============================================================================

/-- Exact-`q1` upper companion of `div128_two_step_lower_of_q0_lower_nat`:
    with the high digit pinned exact and the low digit ≤ its true value, the
    composed two-step quotient is ≤ the full floor. -/
theorem div128_two_step_upper_of_q1_exact_q0_le_nat
    (aHi a1 a0 v q1 q0 r1 : Nat)
    (hv_pos : 0 < v)
    (hq1 : q1 = (aHi * 2^32 + a1) / v)
    (hr1 : r1 = (aHi * 2^32 + a1) % v)
    (hq0_le : q0 ≤ (r1 * 2^32 + a0) / v) :
    q1 * 2^32 + q0 ≤ (aHi * 2^64 + a1 * 2^32 + a0) / v := by
  have h_two_step :
      (aHi * 2^64 + a1 * 2^32 + a0) / v =
        ((aHi * 2^32 + a1) / v) * 2^32 +
          ((((aHi * 2^32 + a1) % v) * 2^32 + a0) / v) := by
    set q1t := (aHi * 2^32 + a1) / v with hq1t_def
    set r1t := (aHi * 2^32 + a1) % v with hr1t_def
    set q0t := (r1t * 2^32 + a0) / v with hq0t_def
    set r0t := (r1t * 2^32 + a0) % v with hr0t_def
    have h_decomp_1 : aHi * 2^32 + a1 = v * q1t + r1t := by
      rw [hq1t_def, hr1t_def]; exact (Nat.div_add_mod _ v).symm
    have h_decomp_0 : r1t * 2^32 + a0 = v * q0t + r0t := by
      rw [hq0t_def, hr0t_def]; exact (Nat.div_add_mod _ v).symm
    have h_r0_lt : r0t < v := by rw [hr0t_def]; exact Nat.mod_lt _ hv_pos
    have h_full : aHi * 2^64 + a1 * 2^32 + a0 = r0t + (q1t * 2^32 + q0t) * v := by
      calc aHi * 2^64 + a1 * 2^32 + a0
            = (aHi * 2^32 + a1) * 2^32 + a0 := by ring
        _ = (v * q1t + r1t) * 2^32 + a0 := by rw [h_decomp_1]
        _ = v * q1t * 2^32 + (r1t * 2^32 + a0) := by ring
        _ = v * q1t * 2^32 + (v * q0t + r0t) := by rw [h_decomp_0]
        _ = r0t + (q1t * 2^32 + q0t) * v := by ring
    rw [h_full]
    have h_div : (r0t + (q1t * 2^32 + q0t) * v) / v = q1t * 2^32 + q0t := by
      rw [Nat.add_mul_div_right _ _ hv_pos, Nat.div_eq_of_lt h_r0_lt]; omega
    rw [h_div, hq1t_def, hq0t_def, hr1t_def]
  rw [h_two_step, ← hq1, ← hr1]
  omega

/-- **`div128Quot_v5 ≤ floor`** (exact upper bound), the tight companion of
    `div128Quot_v5_ge_q_true`. Tightens `div128Quot_v5_le_q_true_plus_one`
    using the second-stage exactness `divKTrialCallV5Q0dd_le_q_true_0`. -/
theorem div128Quot_v5_le_q_true
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (div128Quot_v5 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  rw [← divKTrialCallV5QHat_eq_div128Quot_v5]
  let q1 := divKTrialCallV5Q1dd uHi uLo vTop
  let q0 := divKTrialCallV5Q0dd uHi uLo vTop
  let un1 := divKTrialCallV5Un1 uLo
  let un0 := divKTrialCallV5Un0 uLo
  let un21 := divKTrialCallV5Un21 uHi uLo vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  have hq1_eq : q1.toNat = (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat :=
    divKTrialCallV5Q1dd_eq_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have hq0_le : q0.toNat ≤ (un21.toNat * 2^32 + un0.toNat) / vTop.toNat :=
    divKTrialCallV5Q0dd_le_q_true_0 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_un21_eq_r1 : un21.toNat = (uHi.toNat * 2^32 + un1.toNat) % vTop.toNat :=
    divKTrialCallV5Un21_eq_r1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q1_lt : q1.toNat < 2^32 := by
    have h_N_lt : uHi.toNat * 2^32 + un1.toNat < vTop.toNat * 2^32 := by
      have := divKTrialCallV5Un1_lt_pow32 uLo; nlinarith
    have : (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat < 2^32 :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
    omega
  have h_q0_lt : q0.toNat < 2^32 := by
    refine lt_of_le_of_lt ?_ (show (divKTrialCallV5Q0c uHi uLo vTop).toNat < 2^32 from by
      rw [divKTrialCallV5Q0c_eq_algorithm]; exact algorithmQ0cV5_lt_pow32 uHi uLo vTop)
    exact le_trans
      (show q0.toNat ≤ (divKTrialCallV5Q0d uHi uLo vTop).toNat from by
        show (divKTrialCallV5Q0dd uHi uLo vTop).toNat ≤ _
        delta divKTrialCallV5Q0dd; exact div128Quot_phase2b_q0'_le_self _ _ _ _)
      (by unfold divKTrialCallV5Q0d; exact div128Quot_phase2b_q0'_le_self _ _ _ _)
  have h_qhat : (divKTrialCallV5QHat uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat := by
    unfold divKTrialCallV5QHat
    rw [show (32 : BitVec 6).toNat = 32 from by decide]
    exact EvmWord.halfword_combine _ _ h_q1_lt h_q0_lt
  rw [h_qhat]
  have h_uLo : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV5Un1 divKTrialCallV5Un0
    exact div128Quot_vTop_decomp uLo
  have h_core := div128_two_step_upper_of_q1_exact_q0_le_nat
    uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat un21.toNat
    hvTop_pos hq1_eq h_un21_eq_r1 hq0_le
  rw [show uHi.toNat * 2^64 + uLo.toNat = uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat from by
    rw [h_uLo]; ring]
  exact h_core

/-- **`div128Quot_v5 = floor`** — the v5 capped Knuth-D 128/64 division returns
    the exact floor under the call regime + normalisation. From
    `div128Quot_v5_le_q_true` and `div128Quot_v5_ge_q_true`. This is the
    exactness that converts the trial-level `+3` val256 bound into the `+2` the
    n4 addback carry bridge consumes. Bead `wbc4i.8.2.2.7`. -/
theorem div128Quot_v5_eq_q_true
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (div128Quot_v5 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  le_antisymm
    (div128Quot_v5_le_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop)
    (div128Quot_v5_ge_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop)

end EvmAsm.Evm64
