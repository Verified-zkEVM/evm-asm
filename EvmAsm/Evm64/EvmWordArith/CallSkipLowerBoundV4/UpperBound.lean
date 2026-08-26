/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound

  Upper-bound composition helpers for the v4 128/64 trial-call quotient.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

public section

namespace EvmAsm.Evm64

/-- Pure Nat bridge from upper bounds on the two 32-bit quotient digits to
    the full two-half quotient upper bound.

    The high digit must be bounded by the first abstract quotient digit, while
    the low digit may be one above the second abstract quotient digit. The
    result is the desired full quotient `+1` bound. -/
theorem div128_two_step_upper_of_q0_upper_nat
    (aHi a1 a0 v q1 q0 r1 : Nat)
    (hv_pos : 0 < v)
    (hq1_le : q1 ≤ (aHi * 2^32 + a1) / v)
    (hr1 : r1 = (aHi * 2^32 + a1) % v)
    (hq0_le : q0 ≤ (r1 * 2^32 + a0) / v + 1) :
    q1 * 2^32 + q0 ≤
      (aHi * 2^64 + a1 * 2^32 + a0) / v + 1 := by
  have h_two_step :
      (aHi * 2^64 + a1 * 2^32 + a0) / v =
        ((aHi * 2^32 + a1) / v) * 2^32 +
          ((((aHi * 2^32 + a1) % v) * 2^32 + a0) / v) := by
    set q1t := (aHi * 2^32 + a1) / v with hq1t_def
    set r1t := (aHi * 2^32 + a1) % v with hr1t_def
    set q0t := (r1t * 2^32 + a0) / v with hq0t_def
    set r0t := (r1t * 2^32 + a0) % v with hr0t_def
    have h_decomp_1 : aHi * 2^32 + a1 = v * q1t + r1t := by
      rw [hq1t_def, hr1t_def]
      exact (Nat.div_add_mod _ v).symm
    have h_decomp_0 : r1t * 2^32 + a0 = v * q0t + r0t := by
      rw [hq0t_def, hr0t_def]
      exact (Nat.div_add_mod _ v).symm
    have h_r0_lt : r0t < v := by
      rw [hr0t_def]
      exact Nat.mod_lt _ hv_pos
    have h_full :
        aHi * 2^64 + a1 * 2^32 + a0 = r0t + (q1t * 2^32 + q0t) * v := by
      calc
        aHi * 2^64 + a1 * 2^32 + a0
            = (aHi * 2^32 + a1) * 2^32 + a0 := by ring
        _ = (v * q1t + r1t) * 2^32 + a0 := by rw [h_decomp_1]
        _ = v * q1t * 2^32 + (r1t * 2^32 + a0) := by ring
        _ = v * q1t * 2^32 + (v * q0t + r0t) := by rw [h_decomp_0]
        _ = r0t + (q1t * 2^32 + q0t) * v := by ring
    rw [h_full]
    have h_div :
        (r0t + (q1t * 2^32 + q0t) * v) / v = q1t * 2^32 + q0t := by
      rw [Nat.add_mul_div_right _ _ hv_pos, Nat.div_eq_of_lt h_r0_lt]
      omega
    rw [h_div, hq1t_def, hq0t_def, hr1t_def]
  rw [hr1] at hq0_le
  rw [h_two_step]
  omega

/-- Full v4 128/64 quotient upper bound from exact Phase 1 and the Phase-2
    `+1` low-digit upper bound.

    This is the composition form used by later runtime bridges: once `un21`
    is known to be the mathematical first remainder and is in the call-range
    where the low-digit `+1` bound applies, the packed v4 trial quotient is
    at most one above the true 128/64 quotient. -/
theorem div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop : (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (hUn21_eq_r1 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat =
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let un0 := divKTrialCallV4Un0 uLo
  let q1 := divKTrialCallV4Q1dd uHi uLo vTop
  let q0 := divKTrialCallV4Q0dd uHi uLo vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    simpa [dHi, divKTrialCallV4DHi] using
      div128Quot_dHi_ge_pow31 vTop hvTop_ge
  have hdHi_lt : dHi.toNat < 2^32 := by
    unfold dHi divKTrialCallV4DHi
    exact Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have huHi_lt_vTop_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have hUn21_lt_vTop_decomp : un21.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    simpa [un21] using hUn21_lt_vTop
  have h_qhat :
      (div128Quot_v4 uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat := by
    simpa [q1, q0, dHi, dLo, un21] using
      div128Quot_v4_toNat_eq_trialCall_halves_of_un21_lt
        uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
        huHi_lt_vTop_decomp hUn21_lt_vTop_decomp
  have h_q1_le : q1.toNat ≤ (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat := by
    simpa [q1, un1] using
      divKTrialCallV4Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q0_le : q0.toNat ≤ (un21.toNat * 2^32 + un0.toNat) / vTop.toNat + 1 := by
    have h_q0_decomp :=
      divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_un21_lt_pow63
        uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
        (by simpa [un21] using hUn21_lt_pow63)
        hUn21_lt_vTop_decomp
    rw [← h_vTop_decomp] at h_q0_decomp
    simpa [q0, un21, un0, dHi, dLo] using h_q0_decomp
  have h_un21_eq_r1 :
      un21.toNat = (uHi.toNat * 2^32 + un1.toNat) % vTop.toNat := by
    simpa [un21, un1] using hUn21_eq_r1
  have h_upper :=
    div128_two_step_upper_of_q0_upper_nat
      uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat un21.toNat
      hvTop_pos h_q1_le h_un21_eq_r1 h_q0_le
  have h_uLo_decomp : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV4Un1 divKTrialCallV4Un0
    exact div128Quot_vTop_decomp uLo
  have h_left :
      uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat =
        uHi.toNat * 2^64 + uLo.toNat := by
    rw [h_uLo_decomp]
    ring
  rw [h_qhat]
  rw [h_left] at h_upper
  exact h_upper

/-- Full v4 128/64 `+1` upper bound from the Phase-1 low-half no-wrap
    condition.

    The no-wrap condition supplies the `un21 = r1` premise required by
    `div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1`; the remaining range
    hypotheses are kept explicit for downstream runtime/call bridges. -/
theorem div128Quot_v4_le_q_true_plus_one_of_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop : (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  have hUn21_eq_r1 :=
    divKTrialCallV4Un21_eq_r1_of_no_wrap uHi uLo vTop
      hvTop_ge huHi_lt_vTop huHi_lt_pow63 h_no_wrap
  exact div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1
    uHi uLo vTop hvTop_ge huHi_lt_vTop
    hUn21_lt_pow63 hUn21_lt_vTop hUn21_eq_r1

/-- Full v4 128/64 `+1` upper bound in the final Phase-1b high-half-zero
    branch.

    This mirrors the lower-bound exactness surface: `rhatdd` high-half zero
    gives the low-half no-wrap condition, which supplies the mathematical
    first-remainder identity consumed by the upper-bound composition. -/
theorem div128Quot_v4_le_q_true_plus_one_of_rhatdd_hi_zero
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop : (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 := by
  have h_no_wrap :=
    divKTrialCallV4Un21_low_no_wrap_of_rhatdd_hi_zero
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_rhat_hi_zero
  exact div128Quot_v4_le_q_true_plus_one_of_no_wrap
    uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_pow63
    hUn21_lt_pow63 hUn21_lt_vTop h_no_wrap

end EvmAsm.Evm64
