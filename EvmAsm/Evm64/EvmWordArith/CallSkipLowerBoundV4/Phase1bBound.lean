/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase1bBound

  Algorithm-level Phase-1b facts for the v4 2-correction proof.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Algorithm
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Phase2bNoFireBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2.Un21Bridge
import EvmAsm.Evm64.DivMod.LoopBody.TrialCallBounds

namespace EvmAsm.Evm64

open EvmAsm.Rv64 EvmWord

/-- The pre-second-correction Phase-1b quotient `q1'` used by v4. -/
@[irreducible]
def algorithmQ1dV4 (uHi uLo vTop : Word) : Word :=
  algorithmQ1Prime uHi uLo vTop

/-- The pre-second-correction Phase-1b remainder `rhat'` used by v4. -/
@[irreducible]
def algorithmRhatdV4 (uHi uLo vTop : Word) : Word :=
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
  if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc

/-- The Phase-1a corrected quotient before the first Phase-1b dLo check. -/
@[irreducible]
def algorithmQ1cV4 (uHi vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let q1 := rv64_divu uHi dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  if hi1 = 0 then q1 else q1 + signExtend12 4095

/-- The Phase-1a corrected remainder before the first Phase-1b dLo check. -/
@[irreducible]
def algorithmRhatcV4 (uHi vTop : Word) : Word :=
  let dHi := divKTrialCallV4DHi vTop
  let q1 := rv64_divu uHi dHi
  let rhat := uHi - q1 * dHi
  let hi1 := q1 >>> (32 : BitVec 6).toNat
  if hi1 = 0 then rhat else rhat + dHi

/-- The low 64-bit comparison word for the first Phase-1b dLo check. -/
@[irreducible]
def algorithmRhatUn1cV4 (uHi uLo vTop : Word) : Word :=
  (algorithmRhatcV4 uHi vTop <<< (32 : BitVec 6).toNat) ||| divKTrialCallV4Un1 uLo

/-- The first Phase-1b dLo correction guard. -/
@[irreducible]
def algorithmPhase1bFireV4 (uHi uLo vTop : Word) : Prop :=
  BitVec.ult (algorithmRhatUn1cV4 uHi uLo vTop)
    (algorithmQ1cV4 uHi vTop * divKTrialCallV4DLo vTop)

theorem algorithmQ1dV4_unfold (uHi uLo vTop : Word) :
    algorithmQ1dV4 uHi uLo vTop = algorithmQ1Prime uHi uLo vTop := by
  delta algorithmQ1dV4
  rfl

theorem algorithmRhatdV4_unfold (uHi uLo vTop : Word) :
    algorithmRhatdV4 uHi uLo vTop =
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
       if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc) := by
  delta algorithmRhatdV4
  rfl

/-- If the first Phase-1b dLo check does not fire, the pre-second-correction
    quotient is just the Phase-1a corrected quotient. -/
theorem algorithmQ1dV4_eq_q1c_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV4 uHi uLo vTop) :
    algorithmQ1dV4 uHi uLo vTop = algorithmQ1cV4 uHi vTop := by
  delta algorithmPhase1bFireV4 algorithmRhatUn1cV4 algorithmQ1cV4 algorithmRhatcV4 at h_no_fire
  simp [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] at h_no_fire
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime
  delta algorithmQ1cV4
  simp [divKTrialCallV4DHi, h_no_fire]

/-- If the first Phase-1b dLo check does not fire, the pre-second-correction
    remainder is just the Phase-1a corrected remainder. -/
theorem algorithmRhatdV4_eq_rhatc_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (h_no_fire : ¬ algorithmPhase1bFireV4 uHi uLo vTop) :
    algorithmRhatdV4 uHi uLo vTop = algorithmRhatcV4 uHi vTop := by
  delta algorithmPhase1bFireV4 algorithmRhatUn1cV4 algorithmQ1cV4 algorithmRhatcV4 at h_no_fire
  simp [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] at h_no_fire
  rw [algorithmRhatdV4_unfold]
  delta algorithmRhatcV4
  simp [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1, h_no_fire]

/-- Phase-1b Euclidean identity for the v4 pre-second-correction pair. -/
theorem algorithmQ1dV4_rhatd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
      (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat := by
  have h := algorithmUn21_L2a_wrapped uHi uLo vTop hvTop_ge
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  simpa using h

/-- V4 spelling of the Phase-1b no-wrap fact for the pre-second-correction
    product `q1' * dLo`. -/
theorem algorithmQ1dV4_dLo_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    ((algorithmQ1dV4 uHi uLo vTop) * divKTrialCallV4DLo vTop).toNat =
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat := by
  have h := algorithmUn21_L1b_q1_prime_dLo_no_wrap uHi uLo vTop hvTop_ge huHi_lt_vTop
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4DLo
  simpa using h

/-- The normalized low divisor half extracted by the V4 call wrapper is a
    32-bit value. -/
theorem divKTrialCallV4DLo_lt_pow32 (vTop : Word) :
    (divKTrialCallV4DLo vTop).toNat < 2^32 := by
  unfold divKTrialCallV4DLo
  exact Word_ushiftRight_32_lt_pow32

/-- The high half of the low dividend word extracted by the V4 call wrapper is
    a 32-bit value. -/
theorem divKTrialCallV4Un1_lt_pow32 (uLo : Word) :
    (divKTrialCallV4Un1 uLo).toNat < 2^32 := by
  unfold divKTrialCallV4Un1
  exact Word_ushiftRight_32_lt_pow32

/-- The normalized high divisor half extracted by the V4 call wrapper is a
    32-bit value. -/
theorem divKTrialCallV4DHi_lt_pow32 (vTop : Word) :
    (divKTrialCallV4DHi vTop).toNat < 2^32 := by
  unfold divKTrialCallV4DHi
  exact Word_ushiftRight_32_lt_pow32

/-- The final V4 Phase-1b quotient times the low divisor half does not wrap
    as a 64-bit product under the normalized call preconditions. -/
theorem divKTrialCallV4Q1dd_dLo_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    ((divKTrialCallV4Q1dd uHi uLo vTop) * divKTrialCallV4DLo vTop).toNat =
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat := by
  have h_dHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dHi_lt : (divKTrialCallV4DHi vTop).toNat < 2^32 :=
    divKTrialCallV4DHi_lt_pow32 vTop
  have h_dLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32 :=
    divKTrialCallV4DLo_lt_pow32 vTop
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_uHi_lt_vTop_decomp :
      uHi.toNat <
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have h_q_lt : (divKTrialCallV4Q1dd uHi uLo vTop).toNat < 2^32 :=
    divKTrialCallV4Q1dd_lt_pow32 uHi uLo vTop
      h_dHi_ge h_dHi_lt h_dLo_lt h_uHi_lt_vTop_decomp
  rw [BitVec.toNat_mul]
  apply Nat.mod_eq_of_lt
  nlinarith

/-- Nat formula for the V4 `un21` subtraction over the final Phase-1b
    `q1''`/`rhat''` pair. -/
theorem divKTrialCallV4Un21_toNat
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat =
      (((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat + 2^64 -
        (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat) % 2^64 := by
  rw [divKTrialCallV4Un21_unfold]
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1'' := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat'' := divKTrialCallV4Rhatdd uHi uLo vTop
  let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| un1
  let cu_q1_dlo := q1'' * dLo
  have h_cu_rhat : cu_rhat_un1.toNat =
      (rhat''.toNat % 2^32) * 2^32 + un1.toNat := by
    unfold cu_rhat_un1 un1
    simpa [divKTrialCallV4Un1] using div128Quot_cu_rhat_un1_toNat rhat'' uLo
  have h_cu_q : cu_q1_dlo.toNat =
      q1''.toNat * dLo.toNat := by
    unfold cu_q1_dlo q1'' dLo
    exact divKTrialCallV4Q1dd_dLo_no_wrap uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_local : (cu_rhat_un1 - cu_q1_dlo).toNat =
      ((rhat''.toNat % 2^32) * 2^32 + un1.toNat + 2^64 -
        q1''.toNat * dLo.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, h_cu_rhat, h_cu_q]
    congr 1
    omega
  simpa [dLo, un1, q1'', rhat''] using h_local

/-- Resolve the V4 `un21` modular subtraction formula in the no-wrap case. -/
theorem divKTrialCallV4Un21_toNat_of_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat =
      ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat -
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat := by
  let A := ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
    (divKTrialCallV4Un1 uLo).toNat
  let B := (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
    (divKTrialCallV4DLo vTop).toNat
  have h_formula := divKTrialCallV4Un21_toNat uHi uLo vTop hvTop_ge huHi_lt_vTop
  have hA_lt : A < 2^64 := by
    unfold A
    have h_mod : (divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32 < 2^32 :=
      Nat.mod_lt _ (by decide)
    have h_un : (divKTrialCallV4Un1 uLo).toNat < 2^32 :=
      divKTrialCallV4Un1_lt_pow32 uLo
    nlinarith
  have hBA : B ≤ A := by
    simpa [A, B] using h_no_wrap
  rw [h_formula]
  show (A + 2^64 - B) % 2^64 = A - B
  rw [show A + 2^64 - B = (A - B) + 2^64 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : A - B < 2^64)]

/-- Pure Nat recomposition for the low-half `un21` no-wrap identity. -/
theorem un21_no_wrap_additive_identity_nat
    (rhat q dLo un1 : Nat)
    (h_no_wrap : q * dLo ≤ (rhat % 2^32) * 2^32 + un1) :
    ((rhat % 2^32) * 2^32 + un1 - q * dLo) +
        (rhat / 2^32) * 2^64 + q * dLo =
      rhat * 2^32 + un1 := by
  have h_div_mod : (rhat / 2^32) * 2^32 + rhat % 2^32 = rhat := by
    have := Nat.div_add_mod rhat (2^32)
    linarith
  have h_recompose : rhat * 2^32 =
      (rhat / 2^32) * 2^64 + (rhat % 2^32) * 2^32 := by
    calc rhat * 2^32
        = ((rhat / 2^32) * 2^32 + rhat % 2^32) * 2^32 := by rw [h_div_mod]
      _ = (rhat / 2^32) * 2^64 + (rhat % 2^32) * 2^32 := by ring
  rw [h_recompose]
  omega

/-- Additive V4 `un21` identity in the low-half no-wrap case.

    The high half of `rhat''` is carried explicitly because the machine
    computes `((rhat'' <<< 32) ||| un1)` using only the low 32 bits of
    `rhat''`. -/
theorem divKTrialCallV4Un21_additive_identity_of_no_wrap
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_no_wrap :
      (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat ≤
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat) :
    (divKTrialCallV4Un21 uHi uLo vTop).toNat +
        ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat / 2^32) * 2^64 +
        (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
          (divKTrialCallV4DLo vTop).toNat =
      (divKTrialCallV4Rhatdd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat := divKTrialCallV4Rhatdd uHi uLo vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  change (divKTrialCallV4Un21 uHi uLo vTop).toNat +
        (rhat.toNat / 2^32) * 2^64 + q.toNat * dLo.toNat =
      rhat.toNat * 2^32 + un1.toNat
  have h_un21_local : (divKTrialCallV4Un21 uHi uLo vTop).toNat =
      (rhat.toNat % 2^32) * 2^32 + un1.toNat - q.toNat * dLo.toNat := by
    have h_un21 := divKTrialCallV4Un21_toNat_of_no_wrap
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_no_wrap
    simpa [q, rhat, dLo, un1] using h_un21
  have h_no_wrap_local : q.toNat * dLo.toNat ≤
      (rhat.toNat % 2^32) * 2^32 + un1.toNat := by
    simpa [q, rhat, dLo, un1] using h_no_wrap
  rw [h_un21_local]
  exact un21_no_wrap_additive_identity_nat rhat.toNat q.toNat dLo.toNat un1.toNat
    h_no_wrap_local

/-- Under normalization, the high divisor half extracted by the V4 call wrapper
    is nonzero. -/
theorem divKTrialCallV4DHi_ne_of_ge
    (vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    divKTrialCallV4DHi vTop ≠ 0 := by
  intro hzero
  have hnat : (divKTrialCallV4DHi vTop).toNat = 0 := by rw [hzero]; rfl
  unfold divKTrialCallV4DHi at hnat
  rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow] at hnat
  omega

/-- In the complementary wide-`uHi` regime, Phase 1a's high-half correction
    definitely fires. -/
theorem divKTrialCallV4Q1_hi_ne_zero_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    (rv64_divu uHi (divKTrialCallV4DHi vTop)) >>>
        (32 : BitVec 6).toNat ≠ (0 : Word) := by
  let dHi := divKTrialCallV4DHi vTop
  have hdHi_ne : dHi ≠ 0 := by
    simpa [dHi] using divKTrialCallV4DHi_ne_of_ge vTop hvTop_ge
  have hq_ge : (rv64_divu uHi dHi).toNat ≥ 2^32 := by
    rw [rv64_divu_toNat uHi dHi hdHi_ne]
    apply (Nat.le_div_iff_mul_le ?_).mpr
    · nlinarith [huHi_ge_dHi_pow32]
    · have : dHi.toNat ≠ 0 := by
        intro h0
        exact hdHi_ne (BitVec.eq_of_toNat_eq h0)
      omega
  intro hzero
  have hlt : (rv64_divu uHi dHi).toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rv64_divu uHi dHi)
      ((32 : BitVec 6).toNat)).mp hzero
    simpa using h
  omega

/-- Nat form of subtracting one from a Phase-1a quotient whose high half is
    nonzero. -/
theorem phase1a_q1_dec_toNat_of_hi_ne_zero
    (q1 : Word)
    (hhi : q1 >>> (32 : BitVec 6).toNat ≠ (0 : Word)) :
    (q1 + signExtend12 4095).toNat = q1.toNat - 1 := by
  have hq_ge := (ushiftRight_ne_zero_iff (val := q1) ((32 : BitVec 6).toNat)).mp hhi
  have hq_pos : q1.toNat ≥ 1 := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl] at hq_ge
    omega
  have h_se_toNat : (signExtend12 4095 : Word).toNat = 2^64 - 1 := by decide
  rw [BitVec.toNat_add, h_se_toNat]
  omega

/-- Nat form of the Phase-1b quotient correction when its BLTU guard fires. -/
theorem phase1b_q1_prime_toNat_of_fire
    (q1c dLo rhatUn1 : Word)
    (h_fire : BitVec.ult rhatUn1 (q1c * dLo)) :
    (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat =
      q1c.toNat - 1 := by
  have h_q1c_pos := div128Quot_phase1b_check_implies_q1c_pos q1c dLo rhatUn1 h_fire
  rw [if_pos h_fire]
  rw [BitVec.toNat_add, signExtend12_4095_toNat]
  have h_q1c_lt_word : q1c.toNat - 1 < 2^64 := by have := q1c.isLt; omega
  rw [show q1c.toNat + (2^64 - 1) = (q1c.toNat - 1) + 2^64 from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt h_q1c_lt_word]

/-- If the first Phase-1b correction fires and the pre-correction quotient is
    at most `qTrue + 2`, the corrected quotient is at most `qTrue + 1`. -/
theorem phase1b_q1_prime_le_qtrue_plus_one_of_fire
    (q1c dLo rhatUn1 : Word)
    (qTrue : Nat)
    (h_q1c_le : q1c.toNat ≤ qTrue + 2)
    (h_fire : BitVec.ult rhatUn1 (q1c * dLo)) :
    (if BitVec.ult rhatUn1 (q1c * dLo) then q1c + signExtend12 4095 else q1c).toNat ≤
      qTrue + 1 := by
  rw [phase1b_q1_prime_toNat_of_fire q1c dLo rhatUn1 h_fire]
  omega

/-- In the wide-`uHi` regime, the Phase-1a corrected quotient is `q1 - 1`. -/
theorem divKTrialCallV4Q1c_toNat_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat = q1.toNat - 1 := by
  intro dHi q1 hi1 q1c
  have hhi : q1 >>> (32 : BitVec 6).toNat ≠ (0 : Word) := by
    simpa [dHi, q1] using
      divKTrialCallV4Q1_hi_ne_zero_of_dHi_pow32_le_uHi
        uHi vTop hvTop_ge huHi_ge_dHi_pow32
  show (if hi1 = 0 then q1 else q1 + signExtend12 4095).toNat = q1.toNat - 1
  rw [if_neg hhi]
  exact phase1a_q1_dec_toNat_of_hi_ne_zero q1 hhi

/-- In the wide-`uHi` regime, the Phase-1a corrected quotient is at most
    `2^32`. -/
theorem divKTrialCallV4Q1c_le_pow32_of_dHi_pow32_le_uHi
    (uHi vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_ge_dHi_pow32 :
      (divKTrialCallV4DHi vTop).toNat * 2^32 ≤ uHi.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let q1 := rv64_divu uHi dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    q1c.toNat ≤ 2^32 := by
  intro dHi q1 hi1 q1c
  have h_q1c_eq0 := divKTrialCallV4Q1c_toNat_of_dHi_pow32_le_uHi
    uHi vTop hvTop_ge huHi_ge_dHi_pow32
  have h_q1c_eq : q1c.toNat = q1.toNat - 1 := by
    simpa [dHi, q1, hi1, q1c] using h_q1c_eq0
  have hdHi_ne : dHi ≠ 0 := by
    simpa [dHi] using divKTrialCallV4DHi_ne_of_ge vTop hvTop_ge
  have hdHi_pos : 0 < dHi.toNat := by
    have : dHi.toNat ≠ 0 := by
      intro h0
      exact hdHi_ne (BitVec.eq_of_toNat_eq h0)
    omega
  have hdHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have hq1_eq : q1.toNat = uHi.toNat / dHi.toNat := by
    simpa [dHi, q1] using rv64_divu_toNat uHi dHi hdHi_ne
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 +
      (divKTrialCallV4DLo vTop).toNat := by
    unfold dHi divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_dLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32 :=
    divKTrialCallV4DLo_lt_pow32 vTop
  have h_dLo_le_two_dHi_pred : (divKTrialCallV4DLo vTop).toNat ≤
      2 * dHi.toNat - 1 := by
    have hpow : (2^32 : Nat) = 2 * 2^31 := by decide
    omega
  have h_uHi_le0 : uHi.toNat ≤ dHi.toNat * 2^32 + (2 * dHi.toNat - 1) := by
    rw [h_vTop_decomp] at huHi_lt_vTop
    omega
  have h_rhs_le : dHi.toNat * 2^32 + (2 * dHi.toNat - 1) ≤
      dHi.toNat * (2^32 + 1) + (dHi.toNat - 1) := by
    have h_two : 2 * dHi.toNat - 1 = dHi.toNat + (dHi.toNat - 1) := by omega
    rw [h_two]
    ring_nf
    rfl
  have h_uHi_le : uHi.toNat ≤ dHi.toNat * (2^32 + 1) + (dHi.toNat - 1) :=
    le_trans h_uHi_le0 h_rhs_le
  have hq1_le : q1.toNat ≤ 2^32 + 1 := by
    rw [hq1_eq]
    exact (Nat.div_le_iff_le_mul_add_pred hdHi_pos).mpr h_uHi_le
  rw [h_q1c_eq]
  omega

/-- If the first Phase-1b correction fires, the V4 pre-second-correction
    quotient satisfies the Knuth-style `qTrue + 1` upper bound. -/
theorem algorithmQ1dV4_le_qtrue_plus_one_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let dLo := divKTrialCallV4DLo vTop
    let un1 := divKTrialCallV4Un1 uLo
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    BitVec.ult rhatUn1 (q1c * dLo) →
      (algorithmQ1dV4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat + 1 := by
  intro dHi dLo un1 q1 rhat hi1 q1c rhatc rhatUn1 h_fire
  have h_q1c_le0 := algorithmQ1Prime_step3_q1c_le_q_true_1_plus_two
    uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_q1c_le : q1c.toNat ≤
      (uHi.toNat * 2^32 + un1.toNat) / vTop.toNat + 2 := by
    simpa [dHi, dLo, un1, q1, hi1, q1c, divKTrialCallV4DHi,
      divKTrialCallV4DLo, divKTrialCallV4Un1] using h_q1c_le0
  have h_prime_le := phase1b_q1_prime_le_qtrue_plus_one_of_fire
    q1c dLo rhatUn1
    ((uHi.toNat * 2^32 + un1.toNat) / vTop.toNat)
    h_q1c_le h_fire
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime
  simpa [dHi, dLo, un1, q1, rhat, hi1, q1c, rhatc, rhatUn1,
    divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] using h_prime_le

/-- V4 spelling of the generic Phase-1b upper bound `q1' ≤ 2^32 + 1`. -/
theorem algorithmQ1dV4_le_pow32_plus_one
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat ≤ 2^32 + 1 := by
  have hdHi_ge : (divKTrialCallV4DHi vTop).toNat ≥ 2^31 := by
    unfold divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    have h2 : (2^63 : Nat) = 2^31 * 2^32 := by decide
    omega
  have hdLo_lt : (divKTrialCallV4DLo vTop).toNat < 2^32 :=
    divKTrialCallV4DLo_lt_pow32 vTop
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have huHi_lt_vTop_decomp : uHi.toNat <
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
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
  have h := div128Quot_q1_prime_le_pow32_plus_one uHi dHi dLo rhatUn1
    hdHi_ge hdLo_lt huHi_lt_vTop_decomp
  rw [algorithmQ1dV4_unfold]
  unfold algorithmQ1Prime
  simpa [dHi, dLo, un1, q1, rhat, hi1, q1c, rhatc, qDlo, rhatUn1,
    divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] using h

/-- If the high half of `rhat` is zero and `dHi` is a 32-bit halfword, then
    adding `dHi` to `rhat` cannot wrap a 64-bit word. -/
theorem phase2b_rhat_add_dHi_no_wrap_of_hi_zero
    (rhat dHi : Word)
    (h_rhat_hi_zero : rhat >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_dHi_lt : dHi.toNat < 2^32) :
    (rhat + dHi).toNat = rhat.toNat + dHi.toNat := by
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rhat) ((32 : BitVec 6).toNat)).mp
      h_rhat_hi_zero
    simpa using h
  have h_sum_lt : rhat.toNat + dHi.toNat < 2^64 := by omega
  rw [BitVec.toNat_add]
  omega

/-- A true second-correction unsigned comparison against `q * dLo` implies
    the trial quotient `q` is nonzero. -/
theorem phase2b_q_pos_of_fire_ult
    (q dLo lhs : Word)
    (h_ult : BitVec.ult lhs (q * dLo)) :
    q.toNat ≥ 1 := by
  by_contra hq_lt
  push Not at hq_lt
  have hq_nat : q.toNat = 0 := by omega
  have hq0 : q = 0 := BitVec.eq_of_toNat_eq hq_nat
  subst q
  have h_false : ¬ BitVec.ult lhs ((0 : Word) * dLo) := by
    simp [BitVec.ult]
  exact h_false h_ult

/-- The V4 final Phase-1b quotient wrapper is the generic second-correction
    quotient instantiated with the v4 pre-second-correction pair. -/
theorem divKTrialCallV4Q1dd_eq_phase2b_algorithm
    (uHi uLo vTop : Word) :
    divKTrialCallV4Q1dd uHi uLo vTop =
      div128Quot_phase2b_q0'
        (algorithmQ1dV4 uHi uLo vTop)
        (algorithmRhatdV4 uHi uLo vTop)
        (divKTrialCallV4DLo vTop)
        (divKTrialCallV4Un1 uLo) := by
  rw [← div128Quot_phase2b_q0'_and_form]
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4Q1dd
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  rfl

/-- The V4 final Phase-1b remainder wrapper is the generic second-correction
    remainder update instantiated with the v4 pre-second-correction pair. -/
theorem divKTrialCallV4Rhatdd_eq_phase2b_algorithm
    (uHi uLo vTop : Word) :
    divKTrialCallV4Rhatdd uHi uLo vTop =
      (if (algorithmRhatdV4 uHi uLo vTop) >>> (32 : BitVec 6).toNat = (0 : Word) ∧
          BitVec.ult
            (((algorithmRhatdV4 uHi uLo vTop) <<< (32 : BitVec 6).toNat) |||
              divKTrialCallV4Un1 uLo)
            ((algorithmQ1dV4 uHi uLo vTop) * divKTrialCallV4DLo vTop) then
        algorithmRhatdV4 uHi uLo vTop + divKTrialCallV4DHi vTop
       else
        algorithmRhatdV4 uHi uLo vTop) := by
  rw [algorithmQ1dV4_unfold, algorithmRhatdV4_unfold]
  unfold algorithmQ1Prime divKTrialCallV4Rhatdd
  unfold divKTrialCallV4DHi divKTrialCallV4DLo divKTrialCallV4Un1
  rfl

/-- Narrow-call Phase-1b overshoot bound for the pre-second-correction pair.

    This discharges the `h_overshoot_le_vTop` argument of
    `div128Quot_phase2b_q0'_dLo_bound_fire_case` in the
    `div128Quot_phase2b_q0'_dLo_bound_fire_case` once the Knuth-A style
    `q1' ≤ qTrue + 1` bound is available. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_q_le_qtrue_plus_one
    (uHi uLo vTop : Word)
    (h_q_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat + 1)
    (h_phase1b_post :
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
        (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  have h_vTop_decomp : vTop.toNat =
      (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
    unfold divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_qV_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) + vTop.toNat := by
    have h_mul := Nat.mul_le_mul_right vTop.toNat h_q_le
    have h_div_mul :=
      Nat.div_mul_le_self
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) vTop.toNat
    nlinarith
  have h_u_decomp : uHi.toNat * 2^32 =
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 := by
    have h := congrArg (fun x => x * 2^32) h_phase1b_post
    nlinarith [Nat.add_mul
      ((algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat)
      (algorithmRhatdV4 uHi uLo vTop).toNat (2^32)]
  have h_qV_expand :
      (algorithmQ1dV4 uHi uLo vTop).toNat * vTop.toNat =
        (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat := by
    rw [h_vTop_decomp]
    ring
  nlinarith

/-- First-Phase-1b-fire overshoot discharge for the V4
    pre-second-correction pair. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    let dHi := divKTrialCallV4DHi vTop
    let dLo := divKTrialCallV4DLo vTop
    let un1 := divKTrialCallV4Un1 uLo
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| un1
    BitVec.ult rhatUn1 (q1c * dLo) →
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
        (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
          (divKTrialCallV4Un1 uLo).toNat +
          (divKTrialCallV4DHi vTop).toNat * 2^32 +
          (divKTrialCallV4DLo vTop).toNat := by
  intro dHi dLo un1 q1 rhat hi1 q1c rhatc rhatUn1 h_fire
  have h_q_le := algorithmQ1dV4_le_qtrue_plus_one_of_phase1b_fire
    uHi uLo vTop hvTop_ge huHi_lt_vTop
  simp only [] at h_q_le
  exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_q_le_qtrue_plus_one
    uHi uLo vTop
    (h_q_le h_fire)
    (algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge)

/-- If the first Phase-1b correction does not fire because `rhatc` already
    has a nonzero high half, the dLo multiplication check is automatically
    bounded at the Nat level. -/
theorem phase1b_no_fire_dLo_bound_of_rhat_hi_nonzero
    (q1c rhatc dLo un1 : Word)
    (h_q1c_le : q1c.toNat ≤ 2^32)
    (h_dLo_lt : dLo.toNat < 2^32)
    (h_rhat_hi_ne : rhatc >>> (32 : BitVec 6).toNat ≠ (0 : Word)) :
    q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + un1.toNat := by
  have h_rhat_ge : rhatc.toNat ≥ 2^32 := by
    have h := (ushiftRight_ne_zero_iff (val := rhatc) ((32 : BitVec 6).toNat)).mp
      h_rhat_hi_ne
    simpa using h
  have h_dLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
  have h_prod_le : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) :=
    Nat.mul_le_mul h_q1c_le h_dLo_le
  nlinarith

/-- If the first Phase-1b correction does not fire while `rhatc` has zero
    high half, the failed unsigned comparison is exactly the Nat-level dLo
    bound. -/
theorem phase1b_no_fire_dLo_bound_of_rhat_hi_zero
    (q1c rhatc dLo un1 : Word)
    (h_rhat_hi_zero : rhatc >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_un_lt : un1.toNat < 2^32)
    (h_qdlo_no_wrap : (q1c * dLo).toNat = q1c.toNat * dLo.toNat)
    (h_no_fire :
      ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un1) (q1c * dLo)) :
    q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + un1.toNat := by
  have h_rhat_lt : rhatc.toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rhatc) ((32 : BitVec 6).toNat)).mp
      h_rhat_hi_zero
    simpa using h
  have h_le :
      (q1c * dLo).toNat ≤ ((rhatc <<< (32 : BitVec 6).toNat) ||| un1).toNat := by
    have h_not_lt := mt (EvmWord.ult_iff).mpr h_no_fire
    omega
  have h_combine :
      ((rhatc <<< (32 : BitVec 6).toNat) ||| un1).toNat =
        rhatc.toNat * 2^32 + un1.toNat := by
    rw [show ((32 : BitVec 6).toNat : Nat) = 32 from by rfl]
    exact halfword_combine rhatc un1 h_rhat_lt h_un_lt
  omega

/-- Alias-level no-fire dLo bound for the first Phase-1b correction. -/
theorem algorithmQ1cV4_dLo_bound_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_no_fire : ¬ algorithmPhase1bFireV4 uHi uLo vTop) :
    (algorithmQ1cV4 uHi vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatcV4 uHi vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat := by
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  let q1c := algorithmQ1cV4 uHi vTop
  let rhatc := algorithmRhatcV4 uHi vTop
  have h_dHi_ge : dHi.toNat ≥ 2^31 := by
    unfold dHi divKTrialCallV4DHi
    rw [BitVec.toNat_ushiftRight, AddrNorm.bv6_toNat_32, Nat.shiftRight_eq_div_pow]
    omega
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_un_lt : un1.toNat < 2^32 := by
    simpa [un1] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_uHi_lt_vTop_decomp : uHi.toNat < dHi.toNat * 2^32 + dLo.toNat := by
    rw [← h_vTop_decomp]
    exact huHi_lt_vTop
  have h_q1c_le : q1c.toNat ≤ 2^32 := by
    have h := div128Quot_q1c_le_pow32 uHi dHi dLo
      h_dHi_ge h_dLo_lt h_uHi_lt_vTop_decomp
    change (algorithmQ1cV4 uHi vTop).toNat ≤ 2^32
    delta algorithmQ1cV4
    simpa [dHi, divKTrialCallV4DHi] using h
  have h_qdlo_no_wrap : (q1c * dLo).toNat = q1c.toNat * dLo.toNat := by
    rw [BitVec.toNat_mul]
    apply Nat.mod_eq_of_lt
    have h_dLo_le : dLo.toNat ≤ 2^32 - 1 := by omega
    have h_prod_le : q1c.toNat * dLo.toNat ≤ 2^32 * (2^32 - 1) :=
      Nat.mul_le_mul h_q1c_le h_dLo_le
    omega
  have h_no_fire' :
      ¬ BitVec.ult ((rhatc <<< (32 : BitVec 6).toNat) ||| un1) (q1c * dLo) := by
    delta algorithmPhase1bFireV4 algorithmRhatUn1cV4 at h_no_fire
    simpa [q1c, rhatc, dLo, un1] using h_no_fire
  have h_bound : q1c.toNat * dLo.toNat ≤ rhatc.toNat * 2^32 + un1.toNat := by
    by_cases h_rhat_hi_zero : rhatc >>> (32 : BitVec 6).toNat = (0 : Word)
    · exact phase1b_no_fire_dLo_bound_of_rhat_hi_zero q1c rhatc dLo un1
        h_rhat_hi_zero h_un_lt h_qdlo_no_wrap h_no_fire'
    · exact phase1b_no_fire_dLo_bound_of_rhat_hi_nonzero q1c rhatc dLo un1
        h_q1c_le h_dLo_lt h_rhat_hi_zero
  simpa [q1c, rhatc, dLo, un1] using h_bound

/-- First-Phase-1b-no-fire overshoot discharge for the V4
    pre-second-correction pair. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_no_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_no_fire : ¬ algorithmPhase1bFireV4 uHi uLo vTop) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  have h_bound := algorithmQ1cV4_dLo_bound_of_phase1b_no_fire
    uHi uLo vTop hvTop_ge huHi_lt_vTop h_no_fire
  rw [algorithmQ1dV4_eq_q1c_of_phase1b_no_fire uHi uLo vTop h_no_fire,
    algorithmRhatdV4_eq_rhatc_of_phase1b_no_fire uHi uLo vTop h_no_fire]
  exact le_trans h_bound (by omega)

/-- Unconditional overshoot discharge for the V4 pre-second-correction
    Phase-1b pair, by splitting on the first Phase-1b dLo guard. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_closed
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  by_cases h_fire : algorithmPhase1bFireV4 uHi uLo vTop
  · have h := algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_fire
      uHi uLo vTop hvTop_ge huHi_lt_vTop
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo, divKTrialCallV4Un1] using
      h (by
        simpa [algorithmPhase1bFireV4, algorithmRhatUn1cV4, algorithmQ1cV4,
          algorithmRhatcV4, divKTrialCallV4DHi, divKTrialCallV4DLo,
          divKTrialCallV4Un1] using h_fire)
  · exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_phase1b_no_fire
      uHi uLo vTop hvTop_ge huHi_lt_vTop h_fire

/-- Narrow-call Phase-1b overshoot bound for the pre-second-correction pair.

    This discharges the `h_overshoot_le_vTop` argument of
    `div128Quot_phase2b_q0'_dLo_bound_fire_case` in the
    `uHi < dHi * 2^32` sub-regime. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32)
    (h_phase1b_post :
      (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DHi vTop).toNat +
        (algorithmRhatdV4 uHi uLo vTop).toNat = uHi.toNat) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  have h_q_le0 := algorithmQ1Prime_le_q_true_1_plus_one uHi uLo vTop
    hvTop_ge huHi_lt_vTop (by simpa [divKTrialCallV4DHi] using huHi_lt_dHi_pow32)
  have h_q_le :
      (algorithmQ1dV4 uHi uLo vTop).toNat ≤
        (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat + 1 := by
    rw [algorithmQ1dV4_unfold]
    unfold divKTrialCallV4Un1
    simpa using h_q_le0
  exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_q_le_qtrue_plus_one
    uHi uLo vTop h_q_le h_phase1b_post

/-- Narrow-call Phase-1b overshoot bound, with the Phase-1b Euclidean identity
    discharged internally. -/
theorem algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32_closed
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_dHi_pow32 :
      uHi.toNat < (divKTrialCallV4DHi vTop).toNat * 2^32) :
    (algorithmQ1dV4 uHi uLo vTop).toNat * (divKTrialCallV4DLo vTop).toNat ≤
      (algorithmRhatdV4 uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat +
        (divKTrialCallV4DHi vTop).toNat * 2^32 +
        (divKTrialCallV4DLo vTop).toNat := by
  exact algorithmQ1dV4_dLo_overshoot_le_vTop_of_uHi_lt_dHi_pow32
    uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_dHi_pow32
    (algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge)

/-- V4 Phase-1b post-condition after the second correction. -/
theorem divKTrialCallV4_phase1b_dLo_bound
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat ≤
      (divKTrialCallV4Rhatdd uHi uLo vTop).toNat * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat := by
  let q := algorithmQ1dV4 uHi uLo vTop
  let rhat := algorithmRhatdV4 uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un := divKTrialCallV4Un1 uLo
  have h_q_le : q.toNat ≤ 2^32 + 1 := by
    simpa [q] using algorithmQ1dV4_le_pow32_plus_one uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_dLo_lt : dLo.toNat < 2^32 := by
    simpa [dLo] using divKTrialCallV4DLo_lt_pow32 vTop
  have h_un_lt : un.toNat < 2^32 := by
    simpa [un] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_no_wrap_q : (q * dLo).toNat = q.toNat * dLo.toNat := by
    simpa [q, dLo] using algorithmQ1dV4_dLo_no_wrap uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_overshoot : q.toNat * dLo.toNat ≤
      rhat.toNat * 2^32 + un.toNat + dHi.toNat * 2^32 + dLo.toNat := by
    simpa [q, rhat, dHi, dLo, un] using
      algorithmQ1dV4_dLo_overshoot_le_vTop_closed
        uHi uLo vTop hvTop_ge huHi_lt_vTop
  by_cases h_guard : rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo)
  · have h_guard_full := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult⟩ := h_guard
    have h_dHi_lt : dHi.toNat < 2^32 := by
      unfold dHi divKTrialCallV4DHi
      exact Word_ushiftRight_32_lt_pow32
    have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
      phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_rhat_hi_zero h_dHi_lt
    have h_q_pos : q.toNat ≥ 1 :=
      phase2b_q_pos_of_fire_ult q dLo ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_ult
    obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_fire_case
      q rhat dLo dHi un h_no_wrap_rhat h_q_pos h_rhat_hi_zero h_ult h_overshoot
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    change (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat
    rw [h_qeq, if_pos h_guard_full]
    exact h_bound
  · obtain ⟨h_qeq, h_bound⟩ := div128Quot_phase2b_q0'_dLo_bound_no_fire
      q rhat dLo un h_q_le h_dLo_lt h_un_lt h_no_wrap_q h_guard
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    change (div128Quot_phase2b_q0' q rhat dLo un).toNat * dLo.toNat ≤
      (if rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
        BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) then
        rhat + dHi else rhat).toNat * 2^32 + un.toNat
    rw [h_qeq, if_neg h_guard]
    exact h_bound

/-- Final V4 Phase-1b Euclidean identity after the second correction. -/
theorem divKTrialCallV4Q1dd_rhatdd_post
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DHi vTop).toNat +
      (divKTrialCallV4Rhatdd uHi uLo vTop).toNat =
      uHi.toNat := by
  let q := algorithmQ1dV4 uHi uLo vTop
  let rhat := algorithmRhatdV4 uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un := divKTrialCallV4Un1 uLo
  have h_pre : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge
  let guard : Prop := rhat >>> (32 : BitVec 6).toNat = (0 : Word) ∧
    BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) = true
  by_cases h_guard : guard
  · have h_guard_pos : guard := h_guard
    obtain ⟨h_rhat_hi_zero, h_ult_bool⟩ := h_guard
    have h_ult : BitVec.ult ((rhat <<< (32 : BitVec 6).toNat) ||| un) (q * dLo) := by
      simpa using h_ult_bool
    have h_dHi_lt : dHi.toNat < 2^32 := by
      unfold dHi divKTrialCallV4DHi
      exact Word_ushiftRight_32_lt_pow32
    have h_no_wrap_rhat : (rhat + dHi).toNat = rhat.toNat + dHi.toNat :=
      phase2b_rhat_add_dHi_no_wrap_of_hi_zero rhat dHi h_rhat_hi_zero h_dHi_lt
    have h_q_pos : q.toNat ≥ 1 :=
      phase2b_q_pos_of_fire_ult q dLo ((rhat <<< (32 : BitVec 6).toNat) ||| un) h_ult
    have h_q_dec : (q + signExtend12 4095).toNat = q.toNat - 1 := by
      rw [BitVec.toNat_add, signExtend12_4095_toNat]
      omega
    rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    rw [← div128Quot_phase2b_q0'_and_form]
    change (if guard then q + signExtend12 4095 else q).toNat * dHi.toNat +
        (if guard then rhat + dHi else rhat).toNat = uHi.toNat
    rw [if_pos h_guard_pos, if_pos h_guard_pos, h_q_dec, h_no_wrap_rhat]
    have h_rearrange :
        (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat) =
          q.toNat * dHi.toNat + rhat.toNat := by
      have hq_eq : q.toNat = (q.toNat - 1) + 1 := by omega
      calc
        (q.toNat - 1) * dHi.toNat + (rhat.toNat + dHi.toNat)
            = ((q.toNat - 1) * dHi.toNat + dHi.toNat) + rhat.toNat := by omega
        _ = ((q.toNat - 1) + 1) * dHi.toNat + rhat.toNat := by ring
        _ = q.toNat * dHi.toNat + rhat.toNat := by rw [← hq_eq]
    rw [h_rearrange]
    exact h_pre
  · rw [divKTrialCallV4Q1dd_eq_phase2b_algorithm,
      divKTrialCallV4Rhatdd_eq_phase2b_algorithm]
    rw [← div128Quot_phase2b_q0'_and_form]
    change (if guard then q + signExtend12 4095 else q).toNat * dHi.toNat +
        (if guard then rhat + dHi else rhat).toNat = uHi.toNat
    rw [if_neg h_guard, if_neg h_guard]
    exact h_pre

/-- The final V4 Phase-1b digit does not overshoot the abstract first
    128/64 quotient digit. -/
theorem divKTrialCallV4Q1dd_le_q_true_1
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat := by
  let q := divKTrialCallV4Q1dd uHi uLo vTop
  let rhat := divKTrialCallV4Rhatdd uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using divKTrialCallV4Q1dd_rhatdd_post
      uHi uLo vTop hvTop_ge
  have h_dLo_bound : q.toNat * dLo.toNat ≤ rhat.toNat * 2^32 + un1.toNat := by
    simpa [q, rhat, dLo, un1] using divKTrialCallV4_phase1b_dLo_bound
      uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_mul_le :
      q.toNat * vTop.toNat ≤ uHi.toNat * 2^32 + un1.toNat := by
    rw [h_vTop_decomp]
    calc
      q.toNat * (dHi.toNat * 2^32 + dLo.toNat)
          = q.toNat * dHi.toNat * 2^32 + q.toNat * dLo.toNat := by ring
      _ ≤ q.toNat * dHi.toNat * 2^32 + (rhat.toNat * 2^32 + un1.toNat) := by
        omega
      _ = (q.toNat * dHi.toNat + rhat.toNat) * 2^32 + un1.toNat := by ring
      _ = uHi.toNat * 2^32 + un1.toNat := by rw [h_post]
  have hvTop_pos : 0 < vTop.toNat := by omega
  exact (Nat.le_div_iff_mul_le hvTop_pos).2 h_mul_le

/-- Pure quotient fact for the second-correction fire branch: if the
    high-half product check is strict, the abstract quotient digit is
    strictly below the pre-correction digit. -/
theorem phase1b_fire_q_true_1_lt_q_nat
    (uHi un1 dHi dLo q rhat : Nat)
    (h_vTop_pos : 0 < dHi * 2^32 + dLo)
    (h_post : q * dHi + rhat = uHi)
    (h_fire : rhat * 2^32 + un1 < q * dLo) :
    (uHi * 2^32 + un1) / (dHi * 2^32 + dLo) < q := by
  have h_num_lt :
      uHi * 2^32 + un1 < q * (dHi * 2^32 + dLo) := by
    calc
      uHi * 2^32 + un1
          = (q * dHi + rhat) * 2^32 + un1 := by rw [h_post]
      _ = q * dHi * 2^32 + (rhat * 2^32 + un1) := by ring
      _ < q * dHi * 2^32 + q * dLo := by
        exact Nat.add_lt_add_left h_fire _
      _ = q * (dHi * 2^32 + dLo) := by ring
  exact (Nat.div_lt_iff_lt_mul h_vTop_pos).2 h_num_lt

/-- V4 wrapper for `phase1b_fire_q_true_1_lt_q_nat`: when the second
    correction guard fires, the pre-correction digit is strictly above the
    abstract first quotient digit. -/
theorem algorithmQ1dV4_q_true_1_lt_of_phase2b_fire
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_rhat_hi_zero :
      algorithmRhatdV4 uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word))
    (h_ult :
      BitVec.ult (((algorithmRhatdV4 uHi uLo vTop) <<< (32 : BitVec 6).toNat) |||
          divKTrialCallV4Un1 uLo)
        (algorithmQ1dV4 uHi uLo vTop * divKTrialCallV4DLo vTop)) :
    (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat <
      (algorithmQ1dV4 uHi uLo vTop).toNat := by
  let q := algorithmQ1dV4 uHi uLo vTop
  let rhat := algorithmRhatdV4 uHi uLo vTop
  let dHi := divKTrialCallV4DHi vTop
  let dLo := divKTrialCallV4DLo vTop
  let un1 := divKTrialCallV4Un1 uLo
  have h_vTop_decomp : vTop.toNat = dHi.toNat * 2^32 + dLo.toNat := by
    unfold dHi dLo divKTrialCallV4DHi divKTrialCallV4DLo
    exact div128Quot_vTop_decomp vTop
  have h_post : q.toNat * dHi.toNat + rhat.toNat = uHi.toNat := by
    simpa [q, rhat, dHi] using algorithmQ1dV4_rhatd_post uHi uLo vTop hvTop_ge
  have h_rhat_lt : rhat.toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff (val := rhat) ((32 : BitVec 6).toNat)).mp
      (by simpa [rhat] using h_rhat_hi_zero)
    simpa using h
  have h_un1_lt : un1.toNat < 2^32 := by
    simpa [un1] using divKTrialCallV4Un1_lt_pow32 uLo
  have h_lhs_toNat :
      (((rhat <<< (32 : BitVec 6).toNat) ||| un1).toNat) =
        rhat.toNat * 2^32 + un1.toNat := by
    exact EvmWord.halfword_combine rhat un1 h_rhat_lt h_un1_lt
  have h_rhs_toNat :
      (q * dLo).toNat = q.toNat * dLo.toNat := by
    simpa [q, dLo] using algorithmQ1dV4_dLo_no_wrap
      uHi uLo vTop hvTop_ge huHi_lt_vTop
  have h_ult_nat :
      rhat.toNat * 2^32 + un1.toNat < q.toNat * dLo.toNat := by
    have h_word : ((rhat <<< (32 : BitVec 6).toNat) ||| un1).toNat <
        (q * dLo).toNat := by
      simpa [BitVec.ult, q, rhat, dLo, un1] using h_ult
    rw [h_lhs_toNat, h_rhs_toNat] at h_word
    exact h_word
  have h_core := phase1b_fire_q_true_1_lt_q_nat
    uHi.toNat un1.toNat dHi.toNat dLo.toNat q.toNat rhat.toNat
    (by rw [← h_vTop_decomp]; omega)
    h_post h_ult_nat
  rw [← h_vTop_decomp] at h_core
  simpa [q, dHi, dLo, un1] using h_core

/-- Under the call-reachable `uHi < 2^63` condition, the final V4
    Phase-1b digit does not undershoot the abstract first quotient digit. -/
theorem divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_pow63
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63) :
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
  have huHi_lt_dHi_pow32 : uHi.toNat < dHi.toNat * 2^32 := by
    have h_ge : dHi.toNat * 2^32 ≥ 2^63 := by
      have hmul := Nat.mul_le_mul_right (2^32) h_dHi_ge
      have hpow : (2^31 : Nat) * 2^32 = 2^63 := by decide
      omega
    omega
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

/-- Under the call-reachable `uHi < 2^63` condition, the final V4
    Phase-1b digit is exactly the abstract first quotient digit. -/
theorem divKTrialCallV4Q1dd_eq_q_true_1_of_uHi_lt_pow63
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat =
      (uHi.toNat * 2^32 + (divKTrialCallV4Un1 uLo).toNat) / vTop.toNat := by
  apply le_antisymm
  · exact divKTrialCallV4Q1dd_le_q_true_1 uHi uLo vTop hvTop_ge huHi_lt_vTop
  · exact divKTrialCallV4Q1dd_ge_q_true_1_of_uHi_lt_pow63
      uHi uLo vTop hvTop_ge huHi_lt_vTop huHi_lt_pow63

/-- If the final V4 Phase-1b remainder has zero high half, the final
    dLo-bound is exactly the low-half no-wrap condition for computing
    `un21`. -/
theorem divKTrialCallV4Un21_low_no_wrap_of_rhatdd_hi_zero
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (divKTrialCallV4Q1dd uHi uLo vTop).toNat *
        (divKTrialCallV4DLo vTop).toNat ≤
      ((divKTrialCallV4Rhatdd uHi uLo vTop).toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 uLo).toNat := by
  have h_rhat_lt : (divKTrialCallV4Rhatdd uHi uLo vTop).toNat < 2^32 := by
    have h := (ushiftRight_eq_zero_iff
      (val := divKTrialCallV4Rhatdd uHi uLo vTop)
      ((32 : BitVec 6).toNat)).mp h_rhat_hi_zero
    simpa using h
  have h_bound := divKTrialCallV4_phase1b_dLo_bound
    uHi uLo vTop hvTop_ge huHi_lt_vTop
  rw [Nat.mod_eq_of_lt h_rhat_lt]
  exact h_bound

end EvmAsm.Evm64
