/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q1ddUndershootFromWideUn21

  Bridge lemma toward bead `evm-asm-9iqmw.7.1.4.1.10`:
  when `un21 ≥ vTop`, the Phase-1b output `Q1dd` strictly undershoots
  the abstract Knuth digit `q_true_1`.

  Proof sketch:
    * un21 ≤ rhat''*2^32 + un1 - Q1dd*dLo  (unconditional; from
      `divKTrialCallV4Un21_toNat` + `un21_mod_sub_le_full_remainder_nat`).
    * rhat''*2^32 + un1 - Q1dd*dLo = (uHi*2^32 + un1) - Q1dd*vTop  (from
      Phase-1 Euclidean `divKTrialCallV4Q1dd_rhatdd_post`).
    * If `Q1dd = q_true_1`, then `(uHi*2^32 + un1) - Q1dd*vTop`
      = (uHi*2^32+un1) mod vTop < vTop, so `un21 < vTop` — contradicting
      `un21 ≥ vTop`.
    * Therefore `Q1dd ≠ q_true_1`; combined with the unconditional UB
      `Q1dd ≤ q_true_1`, this gives `Q1dd < q_true_1`.

  Pinned by the counterexample in `Un21WideUHiCounterexample.lean`
  (PR #7077): the conjecture `un21 < vTop` does NOT hold in
  wide-uHi+wide-rhatc, and this bridge converts that to the
  Q1dd-undershoot premise the `un21 ≥ vTop` branch of bead 7.1.4.1
  needs.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Unconditional bound: the machine `un21` is no larger than the
    mathematical first remainder `n - Q1dd*vTop`.  This is the part of
    `divKTrialCallV4Un21_lt_vTop_of_uHi_lt_pow63` that does not require
    `Q1dd = q_true_1`; it works for any `Q1dd ≤ q_true_1`. -/
theorem divKTrialCallV4Un21_le_full_remainder
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) -
        (divKTrialCallV4Q1dd uHi uLo vTop).toNat * vTop.toNat := by
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
  have h_q_le : q.toNat ≤ n / vTop.toNat := by
    simpa [q, n, un1] using
      divKTrialCallV4Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_vTop_pos : 0 < vTop.toNat := by omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_q_lt_pow32 : q.toNat < 2^32 := by
    -- q ≤ n/vTop ≤ 2^32 - 1 follows from n ≤ vTop*2^32 - 1.
    have h_n_lt : n < vTop.toNat * 2^32 := by
      unfold n
      have h_un1_lt' : un1.toNat < 2^32 :=
        divKTrialCallV4Un1_lt_pow32 uLo
      nlinarith [huHi_lt_vTop]
    have h_q_le_div := h_q_le
    have h_div_lt : n / vTop.toNat < 2^32 := by
      rw [Nat.div_lt_iff_lt_mul h_vTop_pos]
      rw [Nat.mul_comm]
      exact h_n_lt
    exact Nat.lt_of_le_of_lt h_q_le_div h_div_lt
  have h_un1_lt : un1.toNat < 2^32 := by
    simpa [un1] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_a_lt : a < 2^64 := by
    unfold a
    have h_mod : rhat.toNat % 2^32 < 2^32 := Nat.mod_lt _ (by decide)
    nlinarith
  have h_b_lt : b < 2^64 := by
    unfold b
    nlinarith [h_q_lt_pow32, h_dLo_lt]
  have h_qv_le_n : q.toNat * vTop.toNat ≤ n := by
    have h_dLo_bound : q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un1.toNat := by
      simpa [q, rhat, dLo, un1] using
        divKTrialCallV4_phase1b_dLo_bound uHi uLo vTop hvTop_ge huHi_lt_vTop
    have h_qv_exp :
        q.toNat * vTop.toNat =
          q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n_exp :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    rw [h_qv_exp, h_n_exp]
    have h_dist : (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat =
        q.toNat * dHi.toNat * 2^32 + (rhat.toNat * 2^32 + un1.toNat) := by ring
    rw [h_dist]
    omega
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
        q.toNat * vTop.toNat =
          q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
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
        q.toNat * vTop.toNat =
          q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by
      rw [h_vTop_decomp]
      ring
    have h_n_exp :
        n = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by
      unfold n
      rw [h_post]
    rw [h_recompose, h_n_exp, h_qv_exp]
    unfold b
    omega
  calc
    (divKTrialCallV4Un21 uHi uLo vTop).toNat
        ≤ (rhat.toNat / 2^32) * 2^64 +
          (rhat.toNat % 2^32) * 2^32 + un1.toNat - b := h_un_le
    _ = n - q.toNat * vTop.toNat := h_remainder_eq

/-- If `un21 ≥ vTop`, then `Q1dd` is strictly less than the abstract
    Knuth digit `q_true_1 = (uHi*2^32 + un1) / vTop`.

    This is the contrapositive of the implicit fact
    "`Q1dd = q_true_1 ⇒ un21 < vTop`": composing the unconditional UB
    `Q1dd ≤ q_true_1` with the un21 upper bound by the mathematical first
    remainder.  Useful for the `un21 ≥ vTop` branch of bead 7.1.4.1
    (the counterexample regime pinned in PR #7077). -/
theorem divKTrialCallV4Q1dd_lt_q_true_1_of_un21_ge_vTop
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (hUn21_ge_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat ≥ vTop.toNat) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat <
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let n := uHi.toNat * 2^32 + un1.toNat
  have hvTop_pos : 0 < vTop.toNat := by omega
  have h_q_le : q.toNat ≤ n / vTop.toNat := by
    simpa [q, n, un1] using
      divKTrialCallV4Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_un21_le_rem :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat ≤ n - q.toNat * vTop.toNat := by
    simpa [n, un1, q] using
      divKTrialCallV4Un21_le_full_remainder uHi uLo vTop hvTop_ge huHi_lt_vTop
  -- Suppose Q1dd = q_true_1: derive un21 < vTop, contradicting un21 ≥ vTop.
  by_contra h_not_lt
  push Not at h_not_lt
  have h_q_eq : q.toNat = n / vTop.toNat := le_antisymm h_q_le h_not_lt
  have h_n_mod : n - q.toNat * vTop.toNat = n % vTop.toNat := by
    have h_div_mod : n / vTop.toNat * vTop.toNat + n % vTop.toNat = n := by
      have := Nat.div_add_mod n vTop.toNat
      linarith
    rw [h_q_eq]
    omega
  have h_mod_lt : n % vTop.toNat < vTop.toNat := Nat.mod_lt n hvTop_pos
  have h_un21_lt :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat := by
    calc
      (divKTrialCallV4Un21 uHi uLo vTop).toNat
          ≤ n - q.toNat * vTop.toNat := h_un21_le_rem
      _ = n % vTop.toNat := h_n_mod
      _ < vTop.toNat := h_mod_lt
  exact absurd h_un21_lt (Nat.not_lt.2 hUn21_ge_vTop)

end EvmAsm.Evm64
