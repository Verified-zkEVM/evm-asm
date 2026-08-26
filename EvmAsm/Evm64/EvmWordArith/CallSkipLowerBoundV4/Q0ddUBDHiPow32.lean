/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Q0ddUBDHiPow32

  Wider-premise variants of the V4 Phase-2 upper-bound (UB) chain:
  `Q0d ≤ q_true_0 + 1` and `Q0dd ≤ q_true_0 + 1` under the strictly
  weaker `un21 < dHi * 2^32` premise (in place of `un21 < 2^63`).

  Parallel to `Un21BoundDHiPow32.lean` (PR #7059) on the lower-bound
  side: the underlying low-level UB
  `div128Quot_q1_prime_le_q_true_1_plus_one` only used `uHi < 2^63` to
  derive `q1 < 2^32` and `rhatc < 2^32`, both of which already have
  Case-A wider variants in `Div128KnuthLower.lean`
  (`div128Quot_q1_lt_pow32_of_uHi_lt_dHi_mul_pow32` and
  `div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32`).  This file
  rebuilds the Phase-1b UB and the V4 Phase-2 wrappers with the wider
  premise.

  Composing with PR #7059's `divKTrialCallV4Un21_lt_vTop_of_uHi_lt_dHi_pow32`
  brings the v4 `+1` floor bound (`div128Quot_v4_le_q_true_plus_one`)
  one step closer to the unconditional discharge of bead `7.1.4.1`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21BoundDHiPow32

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Wider-premise Phase-1b UB: `q1' ≤ q_true_1 + 1` under
    `uHi < dHi * 2^32`.  Identical to
    `div128Quot_q1_prime_le_q_true_1_plus_one` except the only uses of
    the narrower `uHi < 2^63` premise are replaced by their Case-A
    counterparts (`_of_uHi_lt_dHi_mul_pow32`). -/
theorem div128Quot_q1_prime_le_q_true_1_plus_one_of_uHi_lt_dHi_mul_pow32
    (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (h_uHi_lt_dHi_pow32 : uHi.toNat < dHi.toNat * 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
  intro div_un1 q1 rhat hi1 q1c rhatc rhatUn1 q1'
  have h_q1_lt : q1.toNat < 2^32 :=
    div128Quot_q1_lt_pow32_of_uHi_lt_dHi_mul_pow32 uHi dHi hdHi_ne h_uHi_lt_dHi_pow32
  have h_hi1 : hi1 = 0 := by
    apply BitVec.eq_of_toNat_eq
    show (q1 >>> (32 : BitVec 6).toNat).toNat = (0 : Word).toNat
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt h_q1_lt]; rfl
  have h_q1c_eq_q1 : q1c = q1 := by
    show (if hi1 = 0 then q1 else q1 + signExtend12 4095) = q1
    rw [if_pos h_hi1]
  have h_rhatc_eq_rhat : rhatc = rhat := by
    show (if hi1 = 0 then rhat else rhat + dHi) = rhat
    rw [if_pos h_hi1]
  have h_q1c_lt : q1c.toNat < 2^32 := h_q1c_eq_q1 ▸ h_q1_lt
  have h_rhatc_lt : rhatc.toNat < 2^32 :=
    div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32 uHi dHi hdHi_ne
      h_uHi_lt_dHi_pow32 hdHi_lt
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have heq64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
    omega
  have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have h1 : q1c.toNat * dLo.toNat < 2^32 * 2^32 :=
      Nat.mul_lt_mul'' h_q1c_lt hdLo_lt
    have h2 : (2^32 * 2^32 : Nat) = 2^64 := by decide
    omega
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt h_div_un1_lt
  have h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat :=
    div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow_pos : (0 : Nat) < 2^32 := by decide
    have : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow_pos
    exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
  have h_q1c_le_plus_two : q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 := by
    have := div128Quot_q1c_le_q_true_1_plus_two uHi dHi dLo div_un1
      hdHi_ne hdHi_ge hdLo_lt h_div_un1_lt huHi_lt_vTop
    exact this
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    have h_q1' : q1'.toNat = q1c.toNat - 1 := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
            else q1c).toNat = _
      rw [if_pos h_check]
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
      rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · have h_q1' : q1'.toNat = q1c.toNat := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
            else q1c).toNat = _
      rw [if_neg h_check]
    have h_no_check_word : (q1c * dLo).toNat ≤ rhatUn1.toNat := by
      have := h_check
      rw [EvmWord.ult_iff] at this
      omega
    have h_no_check_nat :
        q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + div_un1.toNat := by
      rw [← h_qDlo_eq, ← h_rhatUn1_eq]; exact h_no_check_word
    have h_contra :=
      knuth_theorem_c_strong_contrapositive uHi dHi dLo div_un1 rhatc q1c
        h_eucl h_vTop_pos h_no_check_nat
    omega

/-- V4 Phase-2 Q0d upper bound under the wider `un21 < dHi*2^32` premise.
    Parallel to `divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_pow63`
    with the wider premise. -/
theorem divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_dHi_pow32
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
    div128Quot_q1_prime_le_q_true_1_plus_one_of_uHi_lt_dHi_mul_pow32
      (divKTrialCallV4Un21 uHi uLo vTop)
      (divKTrialCallV4DHi vTop)
      (divKTrialCallV4DLo vTop)
      (uLo <<< (32 : BitVec 6).toNat)
      hdHi_ne hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop
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
    · exact div128Quot_rhatc_lt_pow32_of_uHi_lt_dHi_mul_pow32
        (divKTrialCallV4Un21 uHi uLo vTop)
        (divKTrialCallV4DHi vTop)
        hdHi_ne hUn21_lt_dHi_pow32 hdHi_lt

/-- V4 Phase-2 second-correction UB under the wider `un21 < dHi*2^32`
    premise.  Q0dd ≤ Q0d, so the bound is preserved by the second
    correction. -/
theorem divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_un21_lt_dHi_pow32
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
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have h_q0d_le :=
    divKTrialCallV4Q0d_le_q_true_0_plus_one_of_un21_lt_dHi_pow32
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_dHi_pow32 hUn21_lt_vTop
  -- Q0dd ≤ Q0d (always).
  have h_q0dd_le_q0d := divKTrialCallV4Q0dd_le_q0d uHi uLo vTop
  exact le_trans h_q0dd_le_q0d h_q0d_le

/-- End-to-end V4 `+1` floor bound under the wider `un21 < dHi*2^32`
    premise (in place of the existing `un21 < 2^63`).

    Composition of the always-on Q1dd UB, the new wider Q0dd UB
    (`_of_un21_lt_dHi_pow32`), and the two-step floor compose. -/
theorem div128Quot_v4_le_q_true_plus_one_of_un21_eq_r1_of_un21_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (hUn21_lt_dHi_pow32 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32)
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
      divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_un21_lt_dHi_pow32
        uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt
        (by simpa [un21, dHi] using hUn21_lt_dHi_pow32)
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

end EvmAsm.Evm64
