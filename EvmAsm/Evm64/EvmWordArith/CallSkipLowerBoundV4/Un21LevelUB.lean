/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21LevelUB

  Un21-level Q0dd UB closure for the V4 Knuth-A `+1` chain.

  Combines the narrow-rhat2c upper bound (this file, via a new
  `q1c ≤ 2^32`-compatible Knuth-C variant) with PR #7063's wide-rhat2c
  upper bound to yield an unconditional Q0dd UB under just
  `un21 < vTop` — the upper-bound analog of `div128Quot_q0_prime_ge_q_true_0_un21_level`
  in `CompensationCases.lean`.

  The narrow-rhatc variant differs from PR #7060
  (`div128Quot_q1_prime_le_q_true_1_plus_one_of_uHi_lt_dHi_mul_pow32`) by
  not requiring `uHi < dHi*2^32`: it works for `uHi` (i.e., `un21`)
  anywhere in `[0, vTop)`, but explicitly demands `rhatc < 2^32`
  (instead of having that be implied by `uHi < dHi*2^32`).  When `un21`
  is wide (`un21 ≥ dHi*2^32`), `q0c` can equal `2^32` exactly (not just
  `< 2^32`), so the Knuth-C bridge needs the relaxed `q0c ≤ 2^32`
  variant.

  Combined with the always-on `Q0dd ≤ Q0d` and PR #7063, this closes
  the un21-level UB under just normalisation + `un21 < vTop`,
  symmetric to the LB closure `div128Quot_q0_prime_ge_q_true_0_un21_level`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.WideRhatcUB

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- Knuth-B-level Phase-1b UB under `rhatc < 2^32` (narrow rhat) and
    `uHi < vTop` (any `uHi`, including wide-uHi where `q1c = 2^32`).

    Variant of `div128Quot_q1_prime_le_q_true_1_plus_one_of_uHi_lt_dHi_mul_pow32`
    (PR #7060) that doesn't restrict `uHi < dHi*2^32`: works for wide
    uHi where `q0c` can equal `2^32` exactly.  Uses `div128Quot_q1c_le_pow32`
    (q1c ≤ 2^32) in place of the strict `q1c < 2^32` previously required. -/
theorem div128Quot_q1_prime_le_q_true_1_plus_one_of_rhatc_lt_pow32
    (uHi dHi dLo uLo : Word)
    (hdHi_ne : dHi ≠ 0)
    (hdHi_ge : dHi.toNat ≥ 2^31)
    (hdHi_lt : dHi.toNat < 2^32)
    (hdLo_lt : dLo.toNat < 2^32)
    (huHi_lt_vTop : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat)
    (h_rhatc_lt :
      (let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       rhatc.toNat) < 2^32) :
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then (uHi - q1 * dHi) else (uHi - q1 * dHi) + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
               else q1c
    q1'.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 1 := by
  intro div_un1 q1 hi1 q1c rhatc rhatUn1 q1'
  -- Unfold the let-chain in `h_rhatc_lt` so it sees `q1`/`hi1` from the intros.
  simp only at h_rhatc_lt
  -- q1c ≤ 2^32 (general bound, no q1c < 2^32 needed).
  have h_q1c_le_pow32 : q1c.toNat ≤ 2^32 :=
    div128Quot_q1c_le_pow32 uHi dHi dLo hdHi_ge hdLo_lt huHi_lt_vTop
  -- Narrow rhatc (the new premise).
  have h_rhatc_lt_nat : rhatc.toNat < 2^32 := h_rhatc_lt
  -- div_un1 < 2^32.
  have h_div_un1_lt : div_un1.toNat < 2^32 := by
    show (uLo >>> (32 : BitVec 6).toNat).toNat < 2^32
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have : uLo.toNat < 2^64 := uLo.isLt
    have heq64 : (2^64 : Nat) = 2^32 * 2^32 := by decide
    omega
  -- q1c * dLo < 2^64 (q1c ≤ 2^32, dLo < 2^32 → product ≤ 2^32 * (2^32-1) < 2^64).
  have h_qDlo_le_pow64 : q1c.toNat * dLo.toNat < 2^64 := by
    have h_prod : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) :=
      Nat.mul_le_mul h_q1c_le_pow32 (by omega)
    have h_eq : (2^32 : Nat) * (2^32 - 1) = 2^64 - 2^32 := by decide
    omega
  -- (q1c * dLo).toNat = q1c.toNat * dLo.toNat (no wrap).
  have h_qDlo_eq : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    exact Nat.mod_eq_of_lt h_qDlo_le_pow64
  -- rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat (halfword_combine, needs rhatc<2^32, div_un1<2^32).
  have h_rhatUn1_eq : rhatUn1.toNat = rhatc.toNat * 2^32 + div_un1.toNat := by
    show ((rhatc <<< (32 : BitVec 6).toNat) ||| div_un1).toNat = _
    rw [AddrNorm.bv6_toNat_32]
    exact EvmWord.halfword_combine rhatc div_un1 h_rhatc_lt_nat h_div_un1_lt
  -- Phase 1a Euclidean.
  have h_eucl : q1c.toNat * dHi.toNat + rhatc.toNat = uHi.toNat := by
    simpa [rhatc] using div128Quot_first_round_post uHi dHi hdHi_ne hdHi_lt
  -- vTop > 0.
  have h_vTop_pos : 0 < dHi.toNat * 2^32 + dLo.toNat := by
    have h_dHi_pos : 0 < dHi.toNat := by omega
    have h_pow_pos : (0 : Nat) < 2^32 := by decide
    have : 0 < dHi.toNat * 2^32 := Nat.mul_pos h_dHi_pos h_pow_pos
    exact Nat.lt_of_lt_of_le this (Nat.le_add_right _ _)
  -- q1c ≤ q_true_1 + 2 (Knuth-B, unconditional under call regime).
  have h_q1c_le_plus_two : q1c.toNat ≤
      (uHi.toNat * 2^32 + div_un1.toNat) /
        (dHi.toNat * 2^32 + dLo.toNat) + 2 :=
    div128Quot_q1c_le_q_true_1_plus_two uHi dHi dLo div_un1
      hdHi_ne hdHi_ge hdLo_lt h_div_un1_lt huHi_lt_vTop
  -- Case analysis on Phase 1b check.
  by_cases h_check : BitVec.ult rhatUn1 (q1c * dLo)
  · -- Check fires: q1' = q1c - 1.
    have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_check
    have h_q1' : q1'.toNat = q1c.toNat - 1 := by
      show (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095
            else q1c).toNat = _
      rw [if_pos h_check]
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
      rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]
    omega
  · -- Check doesn't fire: q1' = q1c.  Strong Knuth-C contrapositive.
    have h_q1' : q1'.toNat = q1c.toNat := by
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

/-- V4 Phase-2 Q0d UB in the narrow-rhat2c regime (any un21 < vTop, including wide). -/
theorem divKTrialCallV4Q0d_le_q_true_0_plus_one_of_rhat2c_lt_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (h_rhat2c_lt :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat < 2^32) :
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
  · exact
      div128Quot_q1_prime_le_q_true_1_plus_one_of_rhatc_lt_pow32
        (divKTrialCallV4Un21 uHi uLo vTop)
        (divKTrialCallV4DHi vTop)
        (divKTrialCallV4DLo vTop)
        (uLo <<< (32 : BitVec 6).toNat)
        hdHi_ne hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop
        (by simpa [divKTrialCallV4Rhat2c] using h_rhat2c_lt)
  · -- Discharge `rhat2c >> 32 = 0` from `rhat2c < 2^32`.
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    rw [Nat.div_eq_of_lt]
    · rfl
    · simpa [divKTrialCallV4Rhat2c] using h_rhat2c_lt

/-- V4 Phase-2 Q0dd UB in the narrow-rhat2c regime (any un21 < vTop). -/
theorem divKTrialCallV4Q0dd_le_q_true_0_plus_one_of_rhat2c_lt_pow32
    (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (h_rhat2c_lt :
      (divKTrialCallV4Rhat2c uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      ((divKTrialCallV4Un21 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un0 uLo).toNat) /
        ((divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) + 1 := by
  have h_q0d_le :=
    divKTrialCallV4Q0d_le_q_true_0_plus_one_of_rhat2c_lt_pow32
      uHi uLo vTop hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop h_rhat2c_lt
  exact le_trans (divKTrialCallV4Q0dd_le_q0d uHi uLo vTop) h_q0d_le

end EvmAsm.Evm64
