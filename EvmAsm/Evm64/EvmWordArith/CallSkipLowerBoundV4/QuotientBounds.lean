/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds

  Word-to-Nat bridge wrappers for the v4 trial-call quotient digits.
  These keep downstream exact-quotient proofs phrased in terms of the
  source-of-truth `divKTrialCallV4*` definitions while reusing the generic
  Knuth lower-bound lemmas.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound
import EvmAsm.Evm64.EvmWordArith.Div128KnuthLower
import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Pure Nat bridge from a lower bound on the second half quotient digit to a
    lower bound on the full two-half quotient. -/
theorem div128_two_step_lower_of_q0_lower_nat
    (aHi a1 a0 v q1 q0 r1 : Nat)
    (hv_pos : 0 < v)
    (hq1 : q1 = (aHi * 2^32 + a1) / v)
    (hr1 : r1 = (aHi * 2^32 + a1) % v)
    (hq0_ge : ((r1 * 2^32 + a0) / v) ≤ q0) :
    (aHi * 2^64 + a1 * 2^32 + a0) / v ≤ q1 * 2^32 + q0 := by
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
  rw [h_two_step, ← hq1, ← hr1]
  omega

/-- The v4 trial-call low half-word `un0` is always below `2^32`. -/
theorem divKTrialCallV4Un0_lt_pow32 (uLo : Word) :
    (divKTrialCallV4Un0 uLo).toNat < 2^32 := by
  rw [divKTrialCallV4Un0_eq]
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
  have h_shl : (uLo <<< (32 : BitVec 6).toNat : Word).toNat < 2^64 :=
    (uLo <<< (32 : BitVec 6).toNat : Word).isLt
  exact Nat.div_lt_of_lt_mul (by omega)

/-- Phase 2 first-correction lower bound, wrapped for the v4 trial-call
    definitions.

    This is the v4 analogue of `algorithmQ0Prime_ge_q_true_0`: under
    `un21 < dHi * 2^32`, the first-corrected second quotient digit `Q0d`
    is at least the true second Knuth digit. -/
theorem divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_dHi_mul_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_dHi_mul_pow32
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      uLo
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop

/-- Phase 2 first-correction lower bound, wrapped for the v4 trial-call
    definitions.

    Variant for the complementary easy hypothesis `un21 < 2^63`, matching
    the generic KB-LB8 theorem. -/
theorem divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_pow63
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  exact
    div128Quot_q0_prime_ge_q_true_0_of_un21_lt_pow63
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      uLo
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_pow63 hUn21_lt_vTop

/-- In the Phase-2 tail range, the true second quotient digit is still a
    32-bit half-word. -/
theorem divKTrialCallV4Q0_true_0_lt_pow32_of_un21_lt_vTop
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) < 2^32 := by
  have hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    nlinarith
  have hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32 :=
    divKTrialCallV4Un0_lt_pow32 uLo
  have h_num_lt :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat <
        2^32 * ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) := by
    nlinarith
  exact (Nat.div_lt_iff_lt_mul hDen_pos).mpr h_num_lt

/-- In the Phase-2 tail range `DHi * 2^32 ≤ un21`, the Phase-2a corrected
    digit `Q0c` is at least the maximal half-word value. -/
theorem divKTrialCallV4Q0c_ge_pow32_sub_one_of_dHi_mul_pow32_le_un21
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat) :
    2^32 - 1 ≤ (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  let dHi := divKTrialCallV4DHi vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  have hdHi_ne : dHi ≠ 0 := by
    intro h_eq
    have h_zero : dHi.toNat = 0 := by rw [h_eq]; rfl
    have h_ge : dHi.toNat ≥ 2^31 := by
      simpa [dHi] using hdHi_ge
    omega
  have hq0_ge : 2^32 ≤ q0.toNat := by
    change 2^32 ≤ (rv64_divu un21 dHi).toNat
    rw [rv64_divu_toNat un21 dHi hdHi_ne]
    apply (Nat.le_div_iff_mul_le ?_).mpr
    · have h_ge : dHi.toNat * 2^32 ≤ un21.toNat := by
        simpa [dHi, un21] using hUn21_ge_dHi_pow32
      nlinarith
    · have : 0 < dHi.toNat := by
        have h_ne : dHi.toNat ≠ 0 := by
          intro h_zero
          exact hdHi_ne (BitVec.eq_of_toNat_eq h_zero)
        omega
      exact this
  have hq0_hi_ne : q0 >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    intro h_zero
    have hq0_lt : q0.toNat < 2^32 := by
      have h := (ushiftRight_eq_zero_iff (val := q0) ((32 : BitVec 6).toNat)).mp h_zero
      simpa using h
    omega
  unfold divKTrialCallV4Q0c
  change (if q0 >>> (32 : BitVec 6).toNat = 0 then q0 else q0 + signExtend12 4095).toNat ≥
    2^32 - 1
  rw [if_neg hq0_hi_ne]
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  have h_dec : (q0 + signExtend12 4095).toNat = q0.toNat - 1 := by
    rw [BitVec.toNat_add, h_se_toNat]
    have hq0_lt : q0.toNat < 2^64 := q0.isLt
    omega
  rw [h_dec]
  omega

/-- In the Phase-2 tail range, the Phase-2a corrected digit `Q0c` is at
    most one half-word. -/
theorem divKTrialCallV4Q0c_le_pow32_of_tail
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0c uHi uLo vTop).toNat ≤ 2^32 := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let q0 := rv64_divu un21 dHi
  have hdHi_ne : dHi ≠ 0 := by
    intro h_eq
    have h_zero : dHi.toNat = 0 := by rw [h_eq]; rfl
    have h_ge : dHi.toNat ≥ 2^31 := by
      simpa [dHi] using hdHi_ge
    omega
  have hq0_ge : 2^32 ≤ q0.toNat := by
    change 2^32 ≤ (rv64_divu un21 dHi).toNat
    rw [rv64_divu_toNat un21 dHi hdHi_ne]
    apply (Nat.le_div_iff_mul_le ?_).mpr
    · have h_ge : dHi.toNat * 2^32 ≤ un21.toNat := by
        simpa [dHi, un21] using hUn21_ge_dHi_pow32
      nlinarith
    · have : 0 < dHi.toNat := by
        have h_ne : dHi.toNat ≠ 0 := by
          intro h_zero
          exact hdHi_ne (BitVec.eq_of_toNat_eq h_zero)
        omega
      exact this
  have hq0_le : q0.toNat ≤ 2^32 + 1 := by
    change (rv64_divu un21 dHi).toNat ≤ 2^32 + 1
    rw [rv64_divu_toNat un21 dHi hdHi_ne]
    apply (Nat.div_le_iff_le_mul_add_pred ?_).mpr
    have h_un21_lt : un21.toNat <
        dHi.toNat * 2^32 + dLo.toNat := by
      simpa [dHi, dLo, un21] using hUn21_lt_vTop
    have hdHi_pos : 0 < dHi.toNat := by
      have h_ne : dHi.toNat ≠ 0 := by
        intro h_zero
        exact hdHi_ne (BitVec.eq_of_toNat_eq h_zero)
      omega
    have hdHi_big : 2^32 ≤ 2 * dHi.toNat := by
      nlinarith
    have hdLo_lt_local : dLo.toNat < 2^32 := by
      simpa [dLo] using hdLo_lt
    omega
    · exact Nat.pos_of_ne_zero (by
        intro h_zero
        exact hdHi_ne (BitVec.eq_of_toNat_eq h_zero))
  have hq0_hi_ne : q0 >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    intro h_zero
    have hq0_lt : q0.toNat < 2^32 := by
      have h := (ushiftRight_eq_zero_iff (val := q0) ((32 : BitVec 6).toNat)).mp h_zero
      simpa using h
    omega
  unfold divKTrialCallV4Q0c
  change (if q0 >>> (32 : BitVec 6).toNat = 0 then q0 else q0 + signExtend12 4095).toNat ≤
    2^32
  rw [if_neg hq0_hi_ne]
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  have h_dec : (q0 + signExtend12 4095).toNat = q0.toNat - 1 := by
    rw [BitVec.toNat_add, h_se_toNat]
    have hq0_lt : q0.toNat < 2^64 := q0.isLt
    omega
  rw [h_dec]
  omega

/-- In the Phase-2 tail range, the product `Q0c * DLo` does not wrap. -/
theorem divKTrialCallV4Q0c_mul_DLo_no_wrap_of_tail
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0c uHi uLo vTop *
        divKTrialCallV4DLo vTop).toNat =
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat := by
  have hQ0c_le : (divKTrialCallV4Q0c uHi uLo vTop).toNat ≤ 2^32 :=
    divKTrialCallV4Q0c_le_pow32_of_tail uHi uLo vTop
      hdHi_ge hdLo_lt hUn21_ge_dHi_pow32 hUn21_lt_vTop
  have h_mul_lt :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat < 2^64 := by
    nlinarith
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt h_mul_lt

/-- In the Phase-2 tail range, `Q0c` is a lower bound for the true second
    quotient digit. -/
theorem divKTrialCallV4Q0c_ge_q_true_0_of_dHi_mul_pow32_le_un21
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  have h_true_lt :=
    divKTrialCallV4Q0_true_0_lt_pow32_of_un21_lt_vTop
      uHi uLo vTop hdHi_ge hUn21_lt_vTop
  have h_q0c_ge :=
    divKTrialCallV4Q0c_ge_pow32_sub_one_of_dHi_mul_pow32_le_un21
      uHi uLo vTop hdHi_ge hUn21_ge_dHi_pow32
  omega

/-- Phase 2 first-correction upper bound, wrapped for the v4 trial-call
    definitions.

    Under `un21 < 2^63`, the first-corrected second quotient digit `Q0d`
    is at most one above the true second Knuth digit. This is the upper
    half paired with `divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_pow63`;
    together they show `Q0d` is either exact or one high in this range. -/
theorem divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_pow63
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c divKTrialCallV4Un0
  unfold div128Quot_phase2b_q0'
  rw [if_pos ?_]
  exact
    div128Quot_q1_prime_le_q_true_1_plus_one
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ne hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop hUn21_lt_pow63
  · apply BitVec.eq_of_toNat_eq
    show ((if (rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop)) >>>
            (32 : BitVec 6).toNat = 0 then
          divKTrialCallV4Un21 uHi uLo vTop -
            rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop) *
              divKTrialCallV4DHi vTop
        else
          divKTrialCallV4Un21 uHi uLo vTop -
              rv64_divu (divKTrialCallV4Un21 uHi uLo vTop) (divKTrialCallV4DHi vTop) *
                divKTrialCallV4DHi vTop +
            divKTrialCallV4DHi vTop) >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt]
    · rfl
    · exact div128Quot_rhatc_lt_pow32_of_uHi_lt_pow63
        (divKTrialCallV4Un21 uHi uLo vTop)
        (divKTrialCallV4DHi vTop)
        hdHi_ne hUn21_lt_pow63 hdHi_ge hdHi_lt

/-- Phase 2 second-correction upper bound, wrapped for the v4 trial-call
    definitions.

    The final second quotient digit `Q0dd` is either `Q0d` or `Q0d - 1`;
    therefore the `Q0d ≤ q_true + 1` bound is preserved by the second
    correction. -/
theorem divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_un21_lt_pow63
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_pow63 : (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have h_q0d_le :=
    divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_pow63
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_pow63 hUn21_lt_vTop
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  by_cases h_hi :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)
  · rw [if_pos h_hi]
    by_cases h_ult :
        BitVec.ult
          ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV4Un0 uLo)
          (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)
    · rw [if_pos h_ult]
      have hQ0d_ne : divKTrialCallV4Q0d uHi uLo vTop ≠ 0 := by
        intro h_zero
        have h_rhs_zero :
            divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop = (0 : Word) := by
          rw [h_zero]
          simp
        rw [h_rhs_zero] at h_ult
        simp [BitVec.ult] at h_ult
      have hQ0d_pos : 0 < (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
        have h_ne_nat : (divKTrialCallV4Q0d uHi uLo vTop).toNat ≠ 0 := by
          intro h_zero_nat
          exact hQ0d_ne (BitVec.eq_of_toNat_eq h_zero_nat)
        omega
      have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      have h_dec :
          (divKTrialCallV4Q0d uHi uLo vTop + signExtend12 4095).toNat =
            (divKTrialCallV4Q0d uHi uLo vTop).toNat - 1 := by
        rw [BitVec.toNat_add, h_se_toNat]
        have hQ0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^64 :=
          (divKTrialCallV4Q0d uHi uLo vTop).isLt
        omega
      rw [h_dec]
      omega
    · rw [if_neg h_ult]
      exact h_q0d_le
  · rw [if_neg h_hi]
    exact h_q0d_le

/-- V4 second-correction outer-guard no-fire preservation.

    If the high half of `Rhat2d` is nonzero, the second correction in
    `Q0dd` does not run and `Q0dd = Q0d`. Any lower bound already proved
    for `Q0d` therefore transfers unchanged to `Q0dd`. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne
    (uHi uLo vTop : Word)
    (hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_ne :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat ≠ 0) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_neg hRhat2d_hi_ne]
  exact hQ0d_ge

/-- V4 second-correction inner-guard no-fire preservation.

    If `Rhat2d` has zero high half but the product check does not fire, the
    second correction again leaves `Q0dd = Q0d`. This is the companion
    no-fire case to
    `divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne`. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_eq_zero_of_no_ult
    (uHi uLo vTop : Word)
    (hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hNoUlt :
      ¬ BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_pos hRhat2d_hi_zero]
  rw [if_neg hNoUlt]
  exact hQ0d_ge

/-- V4 second-correction fire preservation from a strict-overestimate witness.

    In the correction-fire branch, `Q0dd = Q0d - 1`. If a separate product
    check argument has already established that `Q0d` is strictly above the
    true second digit, then the decrement still leaves `Q0dd` at least the
    true digit. This isolates the small Word-decrement arithmetic from the
    remaining product-check bridge. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_gt_of_fire
    (uHi uLo vTop : Word)
    (hQ0d_gt :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) <
      (divKTrialCallV4Q0d uHi uLo vTop).toNat)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [divKTrialCallV4Q0dd_unfold]
  unfold div128Quot_phase2b_q0'
  rw [if_pos hRhat2d_hi_zero]
  rw [if_pos hUlt]
  have hQ0d_pos : 0 < (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hQ0d_gt
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  have h_dec :
      (divKTrialCallV4Q0d uHi uLo vTop + signExtend12 4095).toNat =
        (divKTrialCallV4Q0d uHi uLo vTop).toNat - 1 := by
    rw [BitVec.toNat_add, h_se_toNat]
    have hQ0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^64 :=
      (divKTrialCallV4Q0d uHi uLo vTop).isLt
    omega
  rw [h_dec]
  omega

/-- Nat-level product-check bridge for the v4 Phase-2 second digit.

    This specializes the generic product-check implication to the v4 names:
    once `Q0d` and `Rhat2d` satisfy the Euclidean relation against `un21`,
    a strict product-check failure means `Q0d` is strictly above the true
    second Knuth digit. The remaining Word-level fire case only has to
    convert `BLTU ((Rhat2d << 32) | un0) (Q0d*dLo)` into `hProd_gt`. -/
theorem divKTrialCallV4Q0d_gt_q_true_0_of_prod_gt
    (uHi uLo vTop : Word)
    (hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat)
    (hRhat_eq :
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0d uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat)
    (hQ0d_mul :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hProd_gt :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat >
        (divKTrialCallV4Rhat2d uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) <
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  exact EvmWord.product_check_gt_imp_overestimate
    (divKTrialCallV4Un21 uHi uLo vTop).toNat
    (divKTrialCallV4Un0 uLo).toNat
    (divKTrialCallV4DHi vTop).toNat
    (divKTrialCallV4DLo vTop).toNat
    (divKTrialCallV4Q0d uHi uLo vTop).toNat
    (divKTrialCallV4Rhat2d uHi uLo vTop).toNat
    (2^32)
    hDen_pos hRhat_eq hQ0d_mul hProd_gt

/-- Nat-level product-check bridge for the initial v4 Phase-2 second digit.

    This specializes the generic product-check implication to the v4 names:
    once `Q0c` and `Rhat2c` satisfy the Euclidean relation against `un21`,
    a strict product-check failure means `Q0c` is strictly above the true
    second Knuth digit. -/
theorem divKTrialCallV4Q0c_gt_q_true_0_of_prod_gt
    (uHi uLo vTop : Word)
    (hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat)
    (hRhat_eq :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0c uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat)
    (hQ0c_mul :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hProd_gt :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat >
        (divKTrialCallV4Rhat2c uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) <
    (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  exact EvmWord.product_check_gt_imp_overestimate
    (divKTrialCallV4Un21 uHi uLo vTop).toNat
    (divKTrialCallV4Un0 uLo).toNat
    (divKTrialCallV4DHi vTop).toNat
    (divKTrialCallV4DLo vTop).toNat
    (divKTrialCallV4Q0c uHi uLo vTop).toNat
    (divKTrialCallV4Rhat2c uHi uLo vTop).toNat
    (2^32)
    hDen_pos hRhat_eq hQ0c_mul hProd_gt

/-- Word-to-Nat bridge for the initial v4 Phase-2 product-check fire guard.

    When `Rhat2c` is a 32-bit value, the half-word combine
    `(Rhat2c << 32) | un0` has Nat value `Rhat2c * 2^32 + un0`.
    If the product `Q0c*dLo` is known not to wrap, the Word `BLTU` fire
    guard is exactly the Nat strict product inequality needed for the
    first Phase-2 correction. -/
theorem divKTrialCallV4Q0c_prod_gt_of_ult
    (uHi uLo vTop : Word)
    (hRhat2c_hi_zero :
      divKTrialCallV4Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32)
    (hProd_no_wrap :
      (divKTrialCallV4Q0c uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat =
        (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0c uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    (divKTrialCallV4Q0c uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat >
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat := by
  have hRhat2c_lt : (divKTrialCallV4Rhat2c uHi uLo vTop).toNat < 2^32 := by
    have h_div : (divKTrialCallV4Rhat2c uHi uLo vTop).toNat / 2^32 = 0 := by
      have h_toNat :
          (divKTrialCallV4Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat).toNat = 0 := by
        rw [hRhat2c_hi_zero]
        rfl
      rwa [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h_toNat
    exact (Nat.div_eq_zero_iff.mp h_div).resolve_left (by decide)
  have hUlt_nat :
      (((divKTrialCallV4Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo).toNat) <
        (divKTrialCallV4Q0c uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat := by
    rwa [EvmWord.ult_iff] at hUlt
  rw [hProd_no_wrap] at hUlt_nat
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from rfl] at hUlt_nat
  rw [EvmWord.halfword_combine
        (divKTrialCallV4Rhat2c uHi uLo vTop)
        (divKTrialCallV4Un0 uLo) hRhat2c_lt hUn0_lt] at hUlt_nat
  exact hUlt_nat

/-- Word-to-Nat bridge for the v4 Phase-2 product-check fire guard.

    When `Rhat2d` is a 32-bit value, the half-word combine
    `(Rhat2d << 32) | un0` has Nat value `Rhat2d * 2^32 + un0`.
    If the product `Q0d*dLo` is known not to wrap, the Word `BLTU` fire
    guard is exactly the Nat strict product inequality needed by
    `divKTrialCallV4Q0d_gt_q_true_0_of_prod_gt`. -/
theorem divKTrialCallV4Q0d_prod_gt_of_ult
    (uHi uLo vTop : Word)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32)
    (hProd_no_wrap :
      (divKTrialCallV4Q0d uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat =
        (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat >
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat := by
  have hRhat2d_lt : (divKTrialCallV4Rhat2d uHi uLo vTop).toNat < 2^32 := by
    have h_div : (divKTrialCallV4Rhat2d uHi uLo vTop).toNat / 2^32 = 0 := by
      have h_toNat :
          (divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat).toNat = 0 := by
        rw [hRhat2d_hi_zero]
        rfl
      rwa [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at h_toNat
    exact (Nat.div_eq_zero_iff.mp h_div).resolve_left (by decide)
  have hUlt_nat :
      (((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo).toNat) <
        (divKTrialCallV4Q0d uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat := by
    rwa [EvmWord.ult_iff] at hUlt
  rw [hProd_no_wrap] at hUlt_nat
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from rfl] at hUlt_nat
  rw [EvmWord.halfword_combine
        (divKTrialCallV4Rhat2d uHi uLo vTop)
        (divKTrialCallV4Un0 uLo) hRhat2d_lt hUn0_lt] at hUlt_nat
  exact hUlt_nat

/-- The V4 Phase-2 product `Q0d * DLo` does not wrap when `un21 < vTop`.

    This packages the standard `Q0d < 2^32` and `DLo < 2^32` bounds into the
    no-wrap equality consumed by `divKTrialCallV4Q0d_prod_gt_of_ult`. -/
theorem divKTrialCallV4Q0d_mul_DLo_no_wrap
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0d uHi uLo vTop *
        divKTrialCallV4DLo vTop).toNat =
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat := by
  have hQ0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^32 :=
    divKTrialCallV4Q0d_lt_pow32 uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop
  have h_mul_lt :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat < 2^64 := by
    nlinarith
  rw [BitVec.toNat_mul]
  exact Nat.mod_eq_of_lt h_mul_lt

/-- V4 Phase-2 initial Euclidean postcondition.

    Before the first Phase-2 product check, `Q0c` and `Rhat2c` divide `un21`
    by the high divisor digit `DHi`: `Q0c * DHi + Rhat2c = un21`. -/
theorem divKTrialCallV4Q0c_Rhat2c_post
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Q0c uHi uLo vTop).toNat *
        (divKTrialCallV4DHi vTop).toNat +
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat =
    (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  unfold divKTrialCallV4Q0c divKTrialCallV4Rhat2c
  exact div128Quot_first_round_post
    (divKTrialCallV4Un21 uHi uLo vTop)
    (divKTrialCallV4DHi vTop)
    hdHi_ne hdHi_lt

/-- Consequences of `divKTrialCallV4Q0c_Rhat2c_post` in the shape consumed
    by the product-check bridge. -/
theorem divKTrialCallV4Q0c_Rhat2c_bridge
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Rhat2c uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0c uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat ∧
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have h_post := divKTrialCallV4Q0c_Rhat2c_post uHi uLo vTop hdHi_ge hdHi_lt
  constructor <;> omega

/-- Full initial v4 Phase-2 low-limb product-check bridge.

    Under the tail digit bounds, a fired `BLTU` guard for `Q0c * DLo`
    proves that `Q0c` is strictly larger than the true second quotient digit. -/
theorem divKTrialCallV4Q0c_gt_q_true_0_of_ult
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hRhat2c_hi_zero :
      divKTrialCallV4Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0c uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) <
    (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  have hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    nlinarith
  have hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32 :=
    divKTrialCallV4Un0_lt_pow32 uLo
  have hProd_no_wrap :
      (divKTrialCallV4Q0c uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat =
        (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat :=
    divKTrialCallV4Q0c_mul_DLo_no_wrap_of_tail uHi uLo vTop
      hdHi_ge hdLo_lt hUn21_ge_dHi_pow32 hUn21_lt_vTop
  have hProd_gt :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat >
        (divKTrialCallV4Rhat2c uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat :=
    divKTrialCallV4Q0c_prod_gt_of_ult uHi uLo vTop
      hRhat2c_hi_zero hUn0_lt hProd_no_wrap hUlt
  have h_bridge := divKTrialCallV4Q0c_Rhat2c_bridge uHi uLo vTop hdHi_ge hdHi_lt
  exact divKTrialCallV4Q0c_gt_q_true_0_of_prod_gt uHi uLo vTop
    hDen_pos h_bridge.1 h_bridge.2 hProd_gt

/-- V4 first-correction lower bound in the Phase-2 tail range.

    In the tail range, `Q0c` is already a lower bound. If the first
    product-check guard does not fire, then `Q0d = Q0c`. If it fires, the
    product-check bridge proves `Q0c` was strictly high, so decrementing once
    still preserves the lower bound. -/
theorem divKTrialCallV4Q0d_ge_q_true_0_of_tail
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  have hQ0c_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0c uHi uLo vTop).toNat :=
    divKTrialCallV4Q0c_ge_q_true_0_of_dHi_mul_pow32_le_un21
      uHi uLo vTop hdHi_ge hUn21_ge_dHi_pow32 hUn21_lt_vTop
  by_cases hRhat2c_hi_zero :
      divKTrialCallV4Rhat2c uHi uLo vTop >>> (32 : BitVec 6).toNat = 0
  · by_cases hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2c uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0c uHi uLo vTop * divKTrialCallV4DLo vTop)
    · have hQ0c_gt :
        ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
            (divKTrialCallV4Un0 uLo).toNat) /
          ((divKTrialCallV4DHi vTop).toNat * 2^32 +
            (divKTrialCallV4DLo vTop).toNat) <
        (divKTrialCallV4Q0c uHi uLo vTop).toNat :=
        divKTrialCallV4Q0c_gt_q_true_0_of_ult uHi uLo vTop
          hdHi_ge hdHi_lt hdLo_lt hUn21_ge_dHi_pow32 hUn21_lt_vTop
          hRhat2c_hi_zero hUlt
      unfold divKTrialCallV4Q0d
      unfold div128Quot_phase2b_q0'
      rw [if_pos hRhat2c_hi_zero]
      rw [if_pos hUlt]
      have hQ0c_pos : 0 < (divKTrialCallV4Q0c uHi uLo vTop).toNat :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) hQ0c_gt
      have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
      have h_dec :
          (divKTrialCallV4Q0c uHi uLo vTop + signExtend12 4095).toNat =
            (divKTrialCallV4Q0c uHi uLo vTop).toNat - 1 := by
        rw [BitVec.toNat_add, h_se_toNat]
        have hQ0c_lt : (divKTrialCallV4Q0c uHi uLo vTop).toNat < 2^64 :=
          (divKTrialCallV4Q0c uHi uLo vTop).isLt
        omega
      rw [h_dec]
      omega
    · unfold divKTrialCallV4Q0d
      unfold div128Quot_phase2b_q0'
      rw [if_pos hRhat2c_hi_zero]
      rw [if_neg hUlt]
      exact hQ0c_ge
  · unfold divKTrialCallV4Q0d
    unfold div128Quot_phase2b_q0'
    rw [if_neg hRhat2c_hi_zero]
    exact hQ0c_ge

/-- V4 Phase-2 first-correction Euclidean postcondition.

    After the first Phase-2 product check, `Q0d` and `Rhat2d` still divide
    `un21` by the high divisor digit `DHi`: `Q0d * DHi + Rhat2d = un21`.
    This is the V4-name wrapper around the generic `div128Quot_phase2b_post`. -/
theorem divKTrialCallV4Q0d_Rhat2d_post
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat *
        (divKTrialCallV4DHi vTop).toNat +
      (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
    (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have hdHi_ne : divKTrialCallV4DHi vTop ≠ 0 := by
    intro h_eq
    rw [h_eq] at hdHi_ge
    simp at hdHi_ge
  have h_post :
      (divKTrialCallV4Q0c uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat +
        (divKTrialCallV4Rhat2c uHi uLo vTop).toNat =
      (divKTrialCallV4Un21 uHi uLo vTop).toNat :=
    divKTrialCallV4Q0c_Rhat2c_post uHi uLo vTop hdHi_ge hdHi_lt
  have h_rhat2c_lt :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat <
        2 * (divKTrialCallV4DHi vTop).toNat := by
    unfold divKTrialCallV4Rhat2c
    exact div128Quot_rhatc_lt_2dHi
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      hdHi_ne hdHi_lt
  unfold divKTrialCallV4Q0d divKTrialCallV4Rhat2d
  exact
    @div128Quot_phase2b_post
      (divKTrialCallV4Un0 uLo)
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      hdHi_lt
      (divKTrialCallV4Q0c uHi uLo vTop)
      (divKTrialCallV4Rhat2c uHi uLo vTop)
      (divKTrialCallV4DLo vTop)
      h_post
      h_rhat2c_lt

/-- Consequences of `divKTrialCallV4Q0d_Rhat2d_post` in the shape consumed
    by the product-check bridge. -/
theorem divKTrialCallV4Q0d_Rhat2d_bridge
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32) :
    (divKTrialCallV4Rhat2d uHi uLo vTop).toNat =
        (divKTrialCallV4Un21 uHi uLo vTop).toNat -
          (divKTrialCallV4Q0d uHi uLo vTop).toNat *
            (divKTrialCallV4DHi vTop).toNat ∧
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DHi vTop).toNat ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
  have h_post := divKTrialCallV4Q0d_Rhat2d_post uHi uLo vTop hdHi_ge hdHi_lt
  constructor <;> omega

/-- Full v4 Phase-2 low-limb product-check bridge.

    Under the standard digit bounds, a fired `BLTU` guard for `Q0d * DLo`
    proves that `Q0d` is strictly larger than the true second quotient digit. -/
theorem divKTrialCallV4Q0d_gt_q_true_0_of_ult
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0)
    (hUlt :
      BitVec.ult
        ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un0 uLo)
        (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) <
    (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  have hDen_pos :
      0 < (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    nlinarith
  have hUn0_lt : (divKTrialCallV4Un0 uLo).toNat < 2^32 :=
    divKTrialCallV4Un0_lt_pow32 uLo
  have hProd_no_wrap :
      (divKTrialCallV4Q0d uHi uLo vTop *
          divKTrialCallV4DLo vTop).toNat =
        (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat :=
    divKTrialCallV4Q0d_mul_DLo_no_wrap uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop
  have hProd_gt :
      (divKTrialCallV4Q0d uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat >
        (divKTrialCallV4Rhat2d uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat :=
    divKTrialCallV4Q0d_prod_gt_of_ult uHi uLo vTop
      hRhat2d_hi_zero hUn0_lt hProd_no_wrap hUlt
  have h_bridge := divKTrialCallV4Q0d_Rhat2d_bridge uHi uLo vTop hdHi_ge hdHi_lt
  exact divKTrialCallV4Q0d_gt_q_true_0_of_prod_gt uHi uLo vTop
    hDen_pos h_bridge.1 h_bridge.2 hProd_gt

/-- V4 second-correction lower bound in the `un21 < DHi * 2^32` range.

    This is the wider easy Phase-2 range where the first-correction lower
    bound is available directly from the high divisor digit. The second
    correction branch split is identical to the `un21 < 2^63` wrapper. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_un21_lt_dHi_mul_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  have hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
    divKTrialCallV4Q0d_ge_q_true_0_of_un21_lt_dHi_mul_pow32 uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop
  by_cases hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0
  · by_cases hUlt :
        BitVec.ult
          ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV4Un0 uLo)
          (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)
    · have hQ0d_gt :
          ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
              (divKTrialCallV4Un0 uLo).toNat) /
            ((divKTrialCallV4DHi vTop).toNat * 2^32 +
              (divKTrialCallV4DLo vTop).toNat) <
          (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
        divKTrialCallV4Q0d_gt_q_true_0_of_ult uHi uLo vTop
          hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop hRhat2d_hi_zero hUlt
      exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_gt_of_fire uHi uLo vTop
        hQ0d_gt hRhat2d_hi_zero hUlt
    · exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_eq_zero_of_no_ult
        uHi uLo vTop hQ0d_ge hRhat2d_hi_zero hUlt
  · exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne
      uHi uLo vTop hQ0d_ge hRhat2d_hi_zero

/-- V4 second-correction lower bound in the Phase-2 tail range.

    This lifts `divKTrialCallV4Q0d_ge_q_true_0_of_tail` through the same
    second-correction branch split used by the earlier range wrappers. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_tail
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
        (divKTrialCallV4Un21 uHi uLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  have hQ0d_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
    divKTrialCallV4Q0d_ge_q_true_0_of_tail uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt hUn21_ge_dHi_pow32 hUn21_lt_vTop
  by_cases hRhat2d_hi_zero :
      divKTrialCallV4Rhat2d uHi uLo vTop >>> (32 : BitVec 6).toNat = 0
  · by_cases hUlt :
        BitVec.ult
          ((divKTrialCallV4Rhat2d uHi uLo vTop <<< (32 : BitVec 6).toNat) |||
            divKTrialCallV4Un0 uLo)
          (divKTrialCallV4Q0d uHi uLo vTop * divKTrialCallV4DLo vTop)
    · have hQ0d_gt :
          ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
              (divKTrialCallV4Un0 uLo).toNat) /
            ((divKTrialCallV4DHi vTop).toNat * 2^32 +
              (divKTrialCallV4DLo vTop).toNat) <
          (divKTrialCallV4Q0d uHi uLo vTop).toNat :=
        divKTrialCallV4Q0d_gt_q_true_0_of_ult uHi uLo vTop
          hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop hRhat2d_hi_zero hUlt
      exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_gt_of_fire uHi uLo vTop
        hQ0d_gt hRhat2d_hi_zero hUlt
    · exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_eq_zero_of_no_ult
        uHi uLo vTop hQ0d_ge hRhat2d_hi_zero hUlt
  · exact divKTrialCallV4Q0dd_ge_q_true_0_of_q0d_ge_of_rhat2d_hi_ne
      uHi uLo vTop hQ0d_ge hRhat2d_hi_zero

/-- V4 second-correction lower bound under the single `un21 < vTop` guard.

    The proof splits on whether `un21` is below `DHi * 2^32`. The low range
    uses the existing easy wrapper; the complementary range is the tail
    wrapper. -/
theorem divKTrialCallV4Q0dd_ge_q_true_0_of_un21_lt_vTop
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un0 uLo).toNat) /
      ((divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat) ≤
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  by_cases hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32
  · exact divKTrialCallV4Q0dd_ge_q_true_0_of_un21_lt_dHi_mul_pow32
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop
  · have hUn21_ge_dHi_pow32 :
        (divKTrialCallV4DHi vTop).toNat * 2^32 ≤
          (divKTrialCallV4Un21 uHi uLo vTop).toNat := by
      omega
    exact divKTrialCallV4Q0dd_ge_q_true_0_of_tail
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_ge_dHi_pow32 hUn21_lt_vTop

/-- V4 `un21` is the first-step mathematical remainder when the low-half
    Phase-1 subtraction does not wrap.

    The additive identity contributes a possible high-half carry
    `(Rhatdd / 2^32) * 2^64`; the hypotheses `Q1dd = q_true_1` and
    `un21 < vTop ≤ 2^64` force that carry to be zero, leaving the ordinary
    remainder. -/
theorem divKTrialCallV4Un21_eq_r1_of_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat := divKTrialCallV4Rhatdd uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let un21 := divKTrialCallV4Un21 uHi uLo vTop
  let n := uHi.toNat * 2^32 + un1.toNat
  have hvTop_pos : 0 < vTop.toNat := by omega
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using divKTrialCallV4Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_q_eq : q.toNat = n / vTop.toNat := by
    simpa [q, n, un1] using
      divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_pow63
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_pow63
  have h_add := divKTrialCallV4Un21_additive_identity_of_no_wrap
    uHi uLo vTop hvTop_ge huHi_lt_vTop h_no_wrap
  have h_n_eq :
      n = q.toNat * vTop.toNat + un21.toNat + (rhat.toNat / 2^32) * 2^64 := by
    have h_qv :
        q.toNat * vTop.toNat =
          q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    change un21.toNat + (rhat.toNat / 2^32) * 2^64 + q.toNat * dLo.toNat =
      rhat.toNat * 2^32 + un1.toNat at h_add
    rw [h_n, h_qv]
    nlinarith [h_add]
  have h_rem_eq : n - q.toNat * vTop.toNat = un21.toNat + (rhat.toNat / 2^32) * 2^64 := by
    omega
  have h_rem_lt : n - q.toNat * vTop.toNat < vTop.toNat := by
    rw [h_q_eq]
    have h_mul_comm : n / vTop.toNat * vTop.toNat =
        vTop.toNat * (n / vTop.toNat) := by ring
    rw [h_mul_comm]
    have h_div_mod : vTop.toNat * (n / vTop.toNat) + n % vTop.toNat = n :=
      Nat.div_add_mod n vTop.toNat
    have h_mod_lt : n % vTop.toNat < vTop.toNat := Nat.mod_lt n hvTop_pos
    omega
  have h_carry_zero : (rhat.toNat / 2^32) * 2^64 = 0 := by
    have hvTop_le : vTop.toNat ≤ 2^64 := Nat.le_of_lt vTop.isLt
    by_contra h_ne
    have h_pos : 0 < (rhat.toNat / 2^32) * 2^64 := Nat.pos_of_ne_zero h_ne
    have h_big : 2^64 ≤ (rhat.toNat / 2^32) * 2^64 := by
      have h_factor_pos : rhat.toNat / 2^32 ≠ 0 := by
        intro h_zero
        rw [h_zero] at h_pos
        simp at h_pos
      have h_factor : 1 ≤ rhat.toNat / 2^32 :=
        Nat.succ_le_of_lt (Nat.pos_of_ne_zero h_factor_pos)
      calc
        2^64 = 1 * 2^64 := by ring
        _ ≤ (rhat.toNat / 2^32) * 2^64 :=
          Nat.mul_le_mul_right (2^64) h_factor
    omega
  have h_un21_rem : un21.toNat = n - q.toNat * vTop.toNat := by
    rw [h_rem_eq, h_carry_zero]
    omega
  have h_mod : n % vTop.toNat = n - q.toNat * vTop.toNat := by
    rw [h_q_eq]
    have h_div_mod : n / vTop.toNat * vTop.toNat + n % vTop.toNat = n := by
      have h := Nat.div_add_mod n vTop.toNat
      simpa [Nat.mul_comm] using h
    omega
  rw [h_mod]
  exact h_un21_rem

/-- Full v4 128/64 lower bound from exact Phase 1 and the Phase-2 lower
    bound, with the `un21`-as-remainder fact supplied explicitly.

    The remaining exact-quotient work is to discharge `hUn21_eq_r1` from the
    machine subtraction path under the final runtime conditions. -/
theorem div128Quot_v4_ge_q_true_of_un21_eq_r1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (hUn21_eq_r1 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat =
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (div128Quot_v4 uHi uLo vTop).toNat := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let un0 := divKTrialCallV4Un0 uLo
  let q1 := divKTrialCallV4Q1dd uHi uLo vTop
  let q0 := divKTrialCallV4Q0dd uHi uLo vTop
  have hvTop_pos : 0 < vTop.toNat := by omega
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have hdHi_lt : dHi.toNat < 2^32 := by
    unfold dHi divKTrialCallV4DHi
    exact Word_ushiftRight_32_lt_pow32
  have hdLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have huHi_lt_vTop_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have hUn21_lt_vTop_decomp :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact hUn21_lt_vTop
  have hq1_eq :
      q1.toNat = (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat := by
    simpa [q1, un1] using
      divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_pow63
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_pow63
  have hq0_ge :
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 + un0.toNat) /
          vTop.toNat ≤ q0.toNat := by
    have h := divKTrialCallV4Q0dd_ge_q_true_0_of_un21_lt_vTop
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop_decomp
    rw [← h_vTop_decomp] at h
    simpa [q0, un0] using h
  have h_qhat :
      (div128Quot_v4 uHi uLo vTop).toNat = q1.toNat * 2^32 + q0.toNat := by
    have h := div128Quot_v4_toNat_eq_trialCall_halves_of_un21_lt
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop_decomp hUn21_lt_vTop_decomp
    simpa [q1, q0] using h
  have h_uLo_decomp : uLo.toNat = un1.toNat * 2^32 + un0.toNat := by
    unfold un1 un0 divKTrialCallV4Un1 divKTrialCallV4Un0
    exact div128Quot_vTop_decomp uLo
  have h_core :
      (uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat) / vTop.toNat ≤
        q1.toNat * 2^32 + q0.toNat := by
    exact div128_two_step_lower_of_q0_lower_nat
      uHi.toNat un1.toNat un0.toNat vTop.toNat q1.toNat q0.toNat
      (divKTrialCallV4Un21 uHi uLo vTop).toNat
      hvTop_pos hq1_eq hUn21_eq_r1 hq0_ge
  have h_left :
      uHi.toNat * 2^64 + uLo.toNat =
        uHi.toNat * 2^64 + un1.toNat * 2^32 + un0.toNat := by
    rw [h_uLo_decomp]
    ring
  rw [h_qhat]
  rw [h_left]
  exact h_core

/-- Exact v4 128/64 quotient when the Phase-2 `un21` value is the first
    mathematical remainder and the matching upper bound has been supplied. -/
theorem div128Quot_v4_eq_q_true_of_un21_eq_r1_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (hUn21_eq_r1 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat =
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) % vTop.toNat)
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  apply le_antisymm
  · exact h_le
  · exact div128Quot_v4_ge_q_true_of_un21_eq_r1 uHi uLo vTop
      hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1

/-- Full v4 128/64 lower bound from exact Phase 1, Phase-2 lower bound, and
    the Phase-1 low-half no-wrap condition. -/
theorem div128Quot_v4_ge_q_true_of_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (div128Quot_v4 uHi uLo vTop).toNat := by
  have hUn21_eq_r1 :=
    divKTrialCallV4Un21_eq_r1_of_no_wrap uHi uLo vTop
      hvTop_ge huHi_lt_vTop huHi_lt_pow63 h_no_wrap
  exact div128Quot_v4_ge_q_true_of_un21_eq_r1 uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1

/-- Exact v4 128/64 quotient from the Phase-1 low-half no-wrap condition
    and the matching upper bound. -/
theorem div128Quot_v4_eq_q_true_of_no_wrap_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat)
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  have hUn21_eq_r1 :=
    divKTrialCallV4Un21_eq_r1_of_no_wrap uHi uLo vTop
      hvTop_ge huHi_lt_vTop huHi_lt_pow63 h_no_wrap
  exact div128Quot_v4_eq_q_true_of_un21_eq_r1_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1 h_le

/-- Full v4 128/64 lower bound when the final Phase-1b remainder has zero
    high half. In this branch the low-half subtraction no-wrap condition
    follows from the existing Phase-1b bound. -/
theorem div128Quot_v4_ge_q_true_of_rhatdd_hi_zero
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
      (div128Quot_v4 uHi uLo vTop).toNat := by
  have h_no_wrap :=
    divKTrialCallV4Un21_low_no_wrap_of_rhatdd_hi_zero
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_rhat_hi_zero
  exact div128Quot_v4_ge_q_true_of_no_wrap uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_no_wrap

/-- Exact v4 128/64 quotient in the final Phase-1b high-half-zero branch,
    assuming the matching normalized upper bound has been supplied. -/
theorem div128Quot_v4_eq_q_true_of_rhatdd_hi_zero_of_le
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_le :
      (div128Quot_v4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  have h_no_wrap :=
    divKTrialCallV4Un21_low_no_wrap_of_rhatdd_hi_zero
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_rhat_hi_zero
  exact div128Quot_v4_eq_q_true_of_no_wrap_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_no_wrap h_le

end EvmAsm.Evm64
