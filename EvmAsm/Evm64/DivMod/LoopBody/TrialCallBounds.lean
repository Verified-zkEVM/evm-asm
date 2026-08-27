module

public import EvmAsm.Evm64.DivMod.LoopBody.TrialCall
public import EvmAsm.Evm64.EvmWordArith.Div128QuotientBounds

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

theorem divKTrialCallV4DHi_eq (vTop : Word) :
    divKTrialCallV4DHi vTop = vTop >>> (32 : BitVec 6).toNat := by
  unfold divKTrialCallV4DHi
  rfl

theorem divKTrialCallV4Un1_eq (uLo : Word) :
    divKTrialCallV4Un1 uLo = uLo >>> (32 : BitVec 6).toNat := by
  unfold divKTrialCallV4Un1
  rfl

theorem divKTrialCallV4Q1dd_le_phase1b (uHi uLo vTop : Word) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat ≤
      (let dHi := divKTrialCallV4DHi vTop
       let dLo := divKTrialCallV4DLo vTop
       let un1 := divKTrialCallV4Un1 uLo
       let q1 := rv64_divu uHi dHi
       let rhat := uHi - q1 * dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
       let rhatc := if hi1 = 0 then rhat else rhat + dHi
       let qDlo := q1c * dLo
       let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
       if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c).toNat := by
  rw [divKTrialCallV4Q1dd_eq_phase2b]
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q1dd_le_q1c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat ≤
      (let dHi := divKTrialCallV4DHi vTop
       let q1 := rv64_divu uHi dHi
       let hi1 := q1 >>> (32 : BitVec 6).toNat
       if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
  let rhatc := if hi1 = 0 then rhat else rhat + dHi
  let qDlo := q1c * dLo
  let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
  let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
  exact le_trans
    (divKTrialCallV4Q1dd_le_phase1b uHi uLo vTop)
    (div128Quot_q1_prime_le_q1c q1c dLo rhatUn1)

theorem divKTrialCallV4Q1dd_lt_pow32 (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (huHi_lt_vTop :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat < 2^32 := by
  exact lt_of_le_of_lt
    (divKTrialCallV4Q1dd_le_phase1b uHi uLo vTop)
    (by
      rw [divKTrialCallV4Un1_eq]
      exact div128Quot_q1_prime_lt_pow32 uHi (divKTrialCallV4DHi vTop)
        (divKTrialCallV4DLo vTop) uLo hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop)

theorem divKTrialCallV4Q0d_le_q0c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0c uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0d
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q0d_lt_pow32 (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^32 := by
  unfold divKTrialCallV4Q0d divKTrialCallV4Q0c divKTrialCallV4Rhat2c
  rw [divKTrialCallV4Un0_eq]
  exact div128Quot_q0_prime_lt_pow32 (divKTrialCallV4Un21 uHi uLo vTop)
    (divKTrialCallV4DHi vTop) (divKTrialCallV4DLo vTop) uLo
    hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop

theorem divKTrialCallV4Q0dd_le_q0d (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0d uHi uLo vTop).toNat := by
  unfold divKTrialCallV4Q0dd
  exact div128Quot_phase2b_q0'_le_self _ _ _ _

theorem divKTrialCallV4Q0dd_le_q0c (uHi uLo vTop : Word) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat ≤
      (divKTrialCallV4Q0c uHi uLo vTop).toNat :=
  le_trans
    (divKTrialCallV4Q0dd_le_q0d uHi uLo vTop)
    (divKTrialCallV4Q0d_le_q0c uHi uLo vTop)

theorem divKTrialCallV4Q0dd_lt_pow32_of_q0c_lt (uHi uLo vTop : Word)
    (hq0c_lt : (divKTrialCallV4Q0c uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat < 2^32 :=
  lt_of_le_of_lt (divKTrialCallV4Q0dd_le_q0c uHi uLo vTop) hq0c_lt

theorem divKTrialCallV4Q0dd_lt_pow32_of_q0d_lt (uHi uLo vTop : Word)
    (hq0d_lt : (divKTrialCallV4Q0d uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV4Q0dd uHi uLo vTop).toNat < 2^32 :=
  lt_of_le_of_lt (divKTrialCallV4Q0dd_le_q0d uHi uLo vTop) hq0d_lt

theorem divKTrialCallV4QHat_toNat_eq (uHi uLo vTop : Word)
    (hq1_lt : (divKTrialCallV4Q1dd uHi uLo vTop).toNat < 2^32)
    (hq0_lt : (divKTrialCallV4Q0dd uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  unfold divKTrialCallV4QHat
  rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
  exact EvmWord.halfword_combine
    (divKTrialCallV4Q1dd uHi uLo vTop)
    (divKTrialCallV4Q0dd uHi uLo vTop) hq1_lt hq0_lt

theorem divKTrialCallV4QHat_toNat_eq_of_q0c_lt (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (huHi_lt_vTop :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hq0c_lt : (divKTrialCallV4Q0c uHi uLo vTop).toNat < 2^32) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  exact divKTrialCallV4QHat_toNat_eq uHi uLo vTop
    (divKTrialCallV4Q1dd_lt_pow32 uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop)
    (divKTrialCallV4Q0dd_lt_pow32_of_q0c_lt uHi uLo vTop hq0c_lt)

theorem div128Quot_v4_toNat_eq_trialCall_halves_of_q0c_lt (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (huHi_lt_vTop :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hq0c_lt : (divKTrialCallV4Q0c uHi uLo vTop).toNat < 2^32) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [← divKTrialCallV4QHat_eq_div128Quot_v4]
  exact divKTrialCallV4QHat_toNat_eq_of_q0c_lt uHi uLo vTop
    hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop hq0c_lt

theorem divKTrialCallV4QHat_toNat_eq_of_un21_lt (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (huHi_lt_vTop :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (divKTrialCallV4QHat uHi uLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  exact divKTrialCallV4QHat_toNat_eq uHi uLo vTop
    (divKTrialCallV4Q1dd_lt_pow32 uHi uLo vTop
      hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop)
    (divKTrialCallV4Q0dd_lt_pow32_of_q0d_lt uHi uLo vTop
      (divKTrialCallV4Q0d_lt_pow32 uHi uLo vTop
        hdHi_ge hdHi_lt hdLo_lt hUn21_lt_vTop))

theorem div128Quot_v4_toNat_eq_trialCall_halves_of_un21_lt (uHi uLo vTop : Word)
    (hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31)
    (hdHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32)
    (hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32)
    (huHi_lt_vTop :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat) :
    (div128Quot_v4 uHi uLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Q0dd uHi uLo vTop).toNat := by
  rw [← divKTrialCallV4QHat_eq_div128Quot_v4]
  exact divKTrialCallV4QHat_toNat_eq_of_un21_lt uHi uLo vTop
    hdHi_ge hdHi_lt hdLo_lt huHi_lt_vTop hUn21_lt_vTop

end EvmAsm.Evm64
