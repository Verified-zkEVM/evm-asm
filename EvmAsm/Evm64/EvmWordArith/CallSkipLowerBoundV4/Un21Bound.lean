/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound

  Final Phase-1b V4 `un21 < vTop` bound, split out of `Phase1bBound`
  to keep the arithmetic helper file under the line-count guardrail.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- The machine low-word subtraction used for `un21` is bounded by the full
    mathematical remainder, even when the low half wraps. -/
theorem un21_mod_sub_le_full_remainder_nat
    (rhat qdLo un1 : Nat)
    (hA_lt : (rhat % 2^32) * 2^32 + un1 < 2^64)
    (hB_lt : qdLo < 2^64)
    (hB_le_full :
      qdLo ≤ (rhat / 2^32) * 2^64 + (rhat % 2^32) * 2^32 + un1) :
    (((rhat % 2^32) * 2^32 + un1 + 2^64 - qdLo) % 2^64) ≤
      (rhat / 2^32) * 2^64 + (rhat % 2^32) * 2^32 + un1 - qdLo := by
  let A := (rhat % 2^32) * 2^32 + un1
  let H := rhat / 2^32
  by_cases h_le : qdLo ≤ A
  · have h_sub_lt : A - qdLo < 2^64 := by omega
    have h_mod : (A + 2^64 - qdLo) % 2^64 = A - qdLo := by
      rw [show A + 2^64 - qdLo = (A - qdLo) + 2^64 by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt h_sub_lt]
    rw [h_mod]
    omega
  · push Not at h_le
    have h_qdLo_le_HA : qdLo ≤ H * 2^64 + A := by
      simpa [A, H, Nat.add_assoc] using hB_le_full
    have h_H_pos : 0 < H := by
      by_contra h_not
      have hH : H = 0 := Nat.eq_zero_of_not_pos h_not
      omega
    have h_sub_lt : A + 2^64 - qdLo < 2^64 := by omega
    have h_mod : (A + 2^64 - qdLo) % 2^64 = A + 2^64 - qdLo := by
      exact Nat.mod_eq_of_lt h_sub_lt
    rw [h_mod]
    have h_H_ge : 1 ≤ H := Nat.succ_le_of_lt h_H_pos
    omega

/-- Under the call-reachable raw hypotheses, the V4 Phase-1b `un21`
    intermediate is strictly below the normalized top divisor limb. -/
theorem divKTrialCallV4Un21_lt_vTop_of_uHi_lt_pow63
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat := divKTrialCallV4Rhatdd uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let n := uHi.toNat * 2^32 + un1.toNat
  let a := (rhat.toNat % 2^32) * 2^32 + un1.toNat
  let b := q.toNat * dLo.toNat
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using divKTrialCallV4Q1dd_rhatdd_post uHi uLo vTop hvTop_ge
  have h_q_eq : q.toNat = n / vTop.toNat := by
    simpa [q, n, un1] using
      divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_pow63
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_pow63
  have h_vTop_pos : 0 < vTop.toNat := by omega
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    unfold dHi divKTrialCallV4DHi
    exact Word_ushiftRight_32_lt_pow32
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_uHi_lt_vTop_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have h_q_lt : q.toNat < 2^32 := by
    simpa [q, dHi, dLo] using divKTrialCallV4Q1dd_lt_pow32
      uHi uLo vTop h_dHi_ge h_dHi_lt h_dLo_lt h_uHi_lt_vTop_decomp
  have h_un1_lt : un1.toNat < 2^32 := by
    simpa [un1] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_a_lt : a < 2^64 := by
    unfold a
    have h_mod : rhat.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    nlinarith
  have h_b_lt : b < 2^64 := by
    unfold b
    nlinarith
  have h_qv_le_n : q.toNat * vTop.toNat ≤ n := by
    rw [h_q_eq]
    exact Nat.div_mul_le_self n vTop.toNat
  have h_b_le_full :
      b ≤ (rhat.toNat / 2^32) * 2^64 + a := by
    have h_recompose : (rhat.toNat / 2^32) * 2^64 +
        (rhat.toNat % 2^32) * 2^32 = rhat.toNat * 2^32 := by
      have h_div_mod : (rhat.toNat / 2^32) * 2^32 + rhat.toNat % 2^32 =
          rhat.toNat := by
        have := Nat.div_add_mod rhat.toNat (2^32)
        linarith
      calc
        (rhat.toNat / 2^32) * 2^64 + (rhat.toNat % 2^32) * 2^32
            = ((rhat.toNat / 2^32) * 2^32 + rhat.toNat % 2^32) * 2^32 := by ring
        _ = rhat.toNat * 2^32 := by rw [h_div_mod]
    have h_full_eq :
        (rhat.toNat / 2^32) * 2^64 + a =
          rhat.toNat * 2^32 + un1.toNat := by
      unfold a
      rw [← Nat.add_assoc, h_recompose]
    have h_qv_exp :
        q.toNat * vTop.toNat = q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n_exp :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    have h_b_le_rhat : b ≤ rhat.toNat * 2^32 + un1.toNat := by
      rw [h_qv_exp, h_n_exp] at h_qv_le_n
      unfold b
      omega
    rw [h_full_eq]
    exact h_b_le_rhat
  have h_un_le :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat ≤
        (rhat.toNat / 2^32) * 2^64 +
          (rhat.toNat % 2^32) * 2^32 + un1.toNat - b := by
    have h_formula := divKTrialCallV4Un21_toNat uHi uLo vTop hvTop_ge huHi_lt_vTop
    have h_a_lt_core :
        (rhat.toNat % 2^32) * 2^32 + un1.toNat < 2^64 := by
      simpa [a] using h_a_lt
    have h_b_lt_core : b < 2^64 := h_b_lt
    have h_b_le_full_core :
        b ≤ (rhat.toNat / 2^32) * 2^64 +
          (rhat.toNat % 2^32) * 2^32 + un1.toNat := by
      simpa [a, Nat.add_assoc] using h_b_le_full
    have h_core := un21_mod_sub_le_full_remainder_nat rhat.toNat b un1.toNat
      h_a_lt_core h_b_lt_core h_b_le_full_core
    rw [h_formula]
    exact h_core
  have h_remainder_eq :
      (rhat.toNat / 2^32) * 2^64 +
          (rhat.toNat % 2^32) * 2^32 + un1.toNat - b =
        n - q.toNat * vTop.toNat := by
    have h_recompose : (rhat.toNat / 2^32) * 2^64 +
        (rhat.toNat % 2^32) * 2^32 = rhat.toNat * 2^32 := by
      have h_div_mod : (rhat.toNat / 2^32) * 2^32 + rhat.toNat % 2^32 =
          rhat.toNat := by
        have := Nat.div_add_mod rhat.toNat (2^32)
        linarith
      calc
        (rhat.toNat / 2^32) * 2^64 + (rhat.toNat % 2^32) * 2^32
            = ((rhat.toNat / 2^32) * 2^32 + rhat.toNat % 2^32) * 2^32 := by ring
        _ = rhat.toNat * 2^32 := by rw [h_div_mod]
    have h_qv_exp :
        q.toNat * vTop.toNat = q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n_exp :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    rw [h_recompose, h_n_exp, h_qv_exp]
    unfold b
    omega
  have h_remainder_lt : n - q.toNat * vTop.toNat < vTop.toNat := by
    rw [h_q_eq]
    have h_mul_comm : n / vTop.toNat * vTop.toNat =
        vTop.toNat * (n / vTop.toNat) := by ring
    rw [h_mul_comm]
    have h_div_mod : vTop.toNat * (n / vTop.toNat) + n % vTop.toNat = n :=
      Nat.div_add_mod n vTop.toNat
    have h_mod_lt : n % vTop.toNat < vTop.toNat := Nat.mod_lt n h_vTop_pos
    omega
  calc
    (divKTrialCallV4Un21 uHi uLo vTop).toNat
        ≤ (rhat.toNat / 2^32) * 2^64 +
          (rhat.toNat % 2^32) * 2^32 + un1.toNat - b := h_un_le
    _ = n - q.toNat * vTop.toNat := h_remainder_eq
    _ < vTop.toNat := h_remainder_lt

/-- Call-level V4 Phase-1b invariant: after the 2-correction algorithm,
    `un21` is strictly below the normalized top divisor limb. -/
theorem un21V4_lt_vTop_of_call
    (a2 a3 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (algorithmUn21V4 u4 u3 b3').toNat < b3'.toNat := by
  intro shift antiShift b3' u4 u3
  have hb3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hu4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hu4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have h_core := divKTrialCallV4Un21_lt_vTop_of_uHi_lt_pow63
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
  have h_alias : algorithmUn21V4 u4 u3 b3' = divKTrialCallV4Un21 u4 u3 b3' := by
    delta algorithmUn21V4
    rfl
  rw [h_alias]
  exact h_core

end EvmAsm.Evm64
