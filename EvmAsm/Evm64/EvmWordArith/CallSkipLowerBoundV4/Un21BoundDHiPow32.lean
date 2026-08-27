/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21BoundDHiPow32

  Strict generalisation of the V4 Phase-1b lower-bound / `un21 < vTop`
  chain, taking `uHi < dHi * 2^32` in place of the existing `uHi < 2^63`
  premise.

  The two premises are related by `2^63 ≤ dHi * 2^32` (from
  `dHi ≥ 2^31` after normalisation), so `uHi < 2^63 → uHi < dHi * 2^32`,
  i.e., the new premise is strictly weaker.  The converse fails when
  `dHi > 2^31` (i.e., `dHi * 2^32 > 2^63`), so this widens the
  applicable regime.

  The existing low-level Phase-1 lower-bound lemma
  `div128Quot_q1_prime_ge_q_true_1_of_uHi_lt_dHi_mul_pow32` already takes
  the wider hypothesis; only the V4 wrappers in `Phase1bBound.lean`
  inherit the narrower `uHi < 2^63`.  This file rebuilds the V4 wrapper
  chain with the wider premise, reusing the existing low-level proofs.

  This is a direct step toward bead `7.1.4.1` (Knuth-A v4 `+1` bound
  under just normalisation + call regime): the un21 < vTop bound is one
  of the running assumptions in `div128Quot_v4_le_floor_plus_one_*`
  upper-bound lemmas in `UpperBound.lean`, and any chain that needs to
  hold under just normalisation + call regime needs to drop
  `uHi < 2^63`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- V4 Phase-1b lower bound under the strictly weaker `uHi < dHi * 2^32`
    premise.  Identical to `divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_pow63`
    except for the premise: the underlying low-level bound
    `algorithmQ1Prime_ge_q_true_1` already takes this wider hypothesis. -/
theorem divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat ≤
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat := by
  let q := algorithmQ1dV4 uHi uLo vTop
  let rhat := algorithmRhatdV4 uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let qTrue := (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have h_dHi_lt : dHi.toNat < 2^32 := by
    unfold dHi divKTrialCallV4DHi
    exact Word_ushiftRight_32_lt_pow32
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_uHi_lt_vTop_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have h_dHi_ge_raw :
      (vTop >>> (32 : BitVec 6).toNat).toNat ≥ 2^31 := by
    simpa [dHi, divKTrialCallV4DHi] using h_dHi_ge
  have h_dHi_lt_raw :
      (vTop >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    simpa [dHi, divKTrialCallV4DHi] using h_dHi_lt
  have h_dLo_lt_raw :
      ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat < 2^32 := by
    simpa [dLo, divKTrialCallV4DLo] using h_dLo_lt
  have huHi_lt_dHi_pow32_raw :
      uHi.toNat < (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 := by
    simpa [dHi, divKTrialCallV4DHi] using huHi_lt_dHi_pow32
  have h_uHi_lt_vTop_decomp_raw :
      uHi.toNat < (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
        ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat := by
    simpa [dHi, dLo, divKTrialCallV4DHi, divKTrialCallV4DLo] using
      h_uHi_lt_vTop_decomp
  have h_q_ge : qTrue ≤ q.toNat := by
    have h := algorithmQ1Prime_ge_q_true_1 uHi uLo vTop
      h_dHi_ge_raw h_dHi_lt_raw h_dLo_lt_raw
      huHi_lt_dHi_pow32_raw h_uHi_lt_vTop_decomp_raw
    have h_den :
        (vTop >>> (32 : BitVec 6).toNat).toNat * 2^32 +
          ((vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat).toNat =
            vTop.toNat := by
      simpa [dHi, dLo, divKTrialCallV4DHi, divKTrialCallV4DLo] using h_vTop_decomp.symm
    rw [h_den] at h
    rw [← algorithmQ1dV4_unfold uHi uLo vTop] at h
    simpa [q, qTrue, un1, divKTrialCallV4Un1] using h
  let guard : Prop := rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un1) (q * dLo) = true
  by_cases h_guard : guard
  · have h_guard_pos : guard := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult_bool⟩ := h_guard
    have h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un1) (q * dLo) := by
      simpa using h_ult_bool
    have h_q_gt : qTrue < q.toNat := by
      have h := algorithmQ1dV4_q_true_1_lt_of_phase2b_fire
        uHi uLo vTop hvTop_ge huHi_lt_vTop
        (by simpa [rhat] using h_rhat_hi_zero)
        (by simpa [q, rhat, dLo, un1] using h_ult)
      simpa [qTrue, q, un1] using h
    have h_q_pos : q.toNat ≥ 1 := by
      have h_pos : 0 < q.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) h_q_gt
      exact Nat.succ_le_of_lt h_pos
    have h_q_dec : (q + signExtend12 4095).toNat = q.toNat - 1 := by
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      omega
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm]
    rw [← div128Quot_phase2b_q0'_and_form]
    change qTrue ≤ (if guard then q + signExtend12 4095 else q).toNat
    rw [if_pos h_guard_pos, h_q_dec]
    omega
  · rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm]
    rw [← div128Quot_phase2b_q0'_and_form]
    change qTrue ≤ (if guard then q + signExtend12 4095 else q).toNat
    rw [if_neg h_guard]
    exact h_q_ge

/-- V4 Phase-1b exact equality under the strictly weaker `uHi < dHi * 2^32`
    premise.  Combines the always-available upper bound
    `divKTrialCallV4Q1dd_le_q_true_1` with the new lower bound. -/
theorem divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat := by
  apply le_antisymm
  · exact divKTrialCallV4Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  · exact divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_dHi_pow32
      uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32

/-- V4 `un21 < vTop` bound under the strictly weaker `uHi < dHi * 2^32`
    premise.  Identical to `divKTrialCallV4Un21_lt_vTop_of_uHi_lt_pow63`
    except for the premise. -/
theorem divKTrialCallV4Un21_lt_vTop_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 : uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
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
      divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_dHi_pow32
        uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
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

end EvmAsm.Evm64
