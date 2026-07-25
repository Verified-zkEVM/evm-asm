/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient

  Floor-shaped exact quotient surfaces for the v4 128/64 trial quotient.
  The heavier lower-bound arithmetic lives in `QuotientBounds`; this split
  module keeps those declarations available under names that match the final
  exact-quotient target without growing the near-cap source file.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.QuotientBounds
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- V4 128/64 floor lower bound when `un21` is the first-step mathematical
    remainder. This is the lower-bound half of the exact floor quotient. -/
theorem div128Quot_v4_ge_floor_of_un21_eq_r1
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
      (div128Quot_v4 uHi uLo vTop).toNat :=
  div128Quot_v4_ge_q_true_of_un21_eq_r1 uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1

/-- V4 128/64 floor `+1` upper bound in the final Phase-1b high-half-zero
    branch. -/
theorem div128Quot_v4_le_floor_plus_one_of_rhatdd_hi_zero
    (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2^63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat)
    (huHi_lt_pow63 : uHi.toNat < 2^63)
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < 2^63)
    (hUn21_lt_vTop :
      (divKTrialCallV4Un21 uHi uLo vTop).toNat < vTop.toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd uHi uLo vTop >>> (32 : BitVec 6).toNat = (0 : Word)) :
    (div128Quot_v4 uHi uLo vTop).toNat ≤
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat + 1 :=
  div128Quot_v4_le_q_true_plus_one_of_rhatdd_hi_zero uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63
    hUn21_lt_pow63 hUn21_lt_vTop h_rhat_hi_zero

/-- Exact v4 128/64 floor quotient when `un21` is the first-step
    mathematical remainder and the matching upper bound has been supplied. -/
theorem div128Quot_v4_eq_floor_of_un21_eq_r1_of_le
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
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_un21_eq_r1_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop hUn21_eq_r1 h_le

/-- Exact v4 128/64 floor quotient from the Phase-1 low-half no-wrap
    condition and the matching upper bound. -/
theorem div128Quot_v4_eq_floor_of_no_wrap_of_le
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
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_no_wrap_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_no_wrap h_le

/-- Exact v4 128/64 floor quotient in the final Phase-1b high-half-zero
    branch, assuming the matching upper bound has been supplied. -/
theorem div128Quot_v4_eq_floor_of_rhatdd_hi_zero_of_le
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
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat :=
  div128Quot_v4_eq_q_true_of_rhatdd_hi_zero_of_le uHi uLo vTop
    hvTop_ge huHi_lt_vTop huHi_lt_pow63 hUn21_lt_vTop h_rhat_hi_zero h_le

/-- V4 call-skip val256 lower bound from an exact 128/64 floor equality.

    This is the qHat-agnostic §B normalization bridge from v1 composed with
    a supplied exactness fact for `div128Quot_v4`. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_floor
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (div128Quot_v4 u4 u3 b3').toNat =
        (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 h_floor
  have h_bridge := q_true_triple_bridge_to_val256_norm
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz
  simp only [] at h_bridge
  rw [h_floor]
  exact h_bridge

/-- V4 call-skip val256 lower bound from explicit `un21 = r1` exactness
    evidence, without requiring the matching 128/64 upper bound. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_un21_eq_r1
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    (divKTrialCallV4Un21 u4 u3 b3').toNat =
      (u4.toNat * 2^32 + (divKTrialCallV4Un1 u3).toNat) % b3'.toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop hUn21_eq_r1
  have hb3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hu4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h_zero | h_pos
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h_zero])
    · exact h_pos
  have hu4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have h_floor_le :
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat ≤
        (div128Quot_v4 u4 u3 b3').toNat :=
    div128Quot_v4_ge_floor_of_un21_eq_r1
      u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
      hUn21_lt_vTop hUn21_eq_r1
  have h_bridge := q_true_triple_bridge_to_val256_norm
    a0 a1 a2 a3 b0 b1 b2 b3 hshift_nz hb3nz
  simp only [] at h_bridge
  exact le_trans h_bridge h_floor_le

/-- V4 call-skip val256 lower bound from the Phase-1 low-half no-wrap
    condition, without requiring the matching 128/64 upper bound. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop h_no_wrap
  have hb3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hu4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h_zero | h_pos
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h_zero])
    · exact h_pos
  have hu4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have hUn21_eq_r1 :=
    divKTrialCallV4Un21_eq_r1_of_no_wrap u4 u3 b3'
      hb3'_ge hu4_lt_b3' hu4_lt_pow63 h_no_wrap
  exact div128Quot_v4_call_skip_ge_val256_div_of_un21_eq_r1
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall
    hUn21_lt_vTop hUn21_eq_r1

/-- V4 call-skip val256 lower bound from runtime call conditions and the
    Phase-1 low-half no-wrap condition.

    This wrapper discharges `un21 < vTop` via the V4 call-path invariant. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_runtime_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 h_no_wrap
  have hUn21_lt_vTop :
      (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat := by
    have h := un21V4_lt_vTop_of_call a2 a3 b2 b3 hb3nz hshift_nz hcall
    simpa [algorithmUn21V4, shift, antiShift, b3', u4, u3] using h
  exact div128Quot_v4_call_skip_ge_val256_div_of_no_wrap
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall
    hUn21_lt_vTop h_no_wrap

/-- V4 call-skip val256 lower bound from the Phase-1 low-half no-wrap
    condition and a supplied 128/64 upper bound. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_no_wrap_of_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat →
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 hUn21_lt_vTop h_no_wrap h_le
  have hb3'_ge : b3'.toNat ≥ 2^63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz _
  have hu4_lt_b3' : u4.toNat < b3'.toNat :=
    isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_shift_pos : 1 ≤ (clzResult b3).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b3).1.toNat with h_zero | h_pos
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h_zero])
    · exact h_pos
  have hu4_lt_pow63 : u4.toNat < 2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b3).1 h_shift_pos
      (clzResult_fst_toNat_le b3)
  have h_floor := div128Quot_v4_eq_floor_of_no_wrap_of_le
    u4 u3 b3' hb3'_ge hu4_lt_b3' hu4_lt_pow63
    hUn21_lt_vTop h_no_wrap h_le
  exact div128Quot_v4_call_skip_ge_val256_div_of_floor
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz h_floor

/-- V4 call-skip val256 lower bound from runtime call conditions, the
    Phase-1 low-half no-wrap condition, and a supplied 128/64 upper bound.

    This wrapper discharges `un21 < vTop` via the V4 call-path invariant. -/
theorem div128Quot_v4_call_skip_ge_val256_div_of_runtime_no_wrap_of_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    (divKTrialCallV4Q1dd u4 u3 b3').toNat *
        (divKTrialCallV4DLo b3').toNat ≤
      ((divKTrialCallV4Rhatdd u4 u3 b3').toNat % 2^32) * 2^32 +
        (divKTrialCallV4Un1 u3).toNat →
    (div128Quot_v4 u4 u3 b3').toNat ≤
      (u4.toNat * 2^64 + u3.toNat) / b3'.toNat →
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
      (div128Quot_v4 u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3 h_no_wrap h_le
  have hUn21_lt_vTop :
      (divKTrialCallV4Un21 u4 u3 b3').toNat < b3'.toNat := by
    have h := un21V4_lt_vTop_of_call a2 a3 b2 b3 hb3nz hshift_nz hcall
    simpa [algorithmUn21V4, shift, antiShift, b3', u4, u3] using h
  exact div128Quot_v4_call_skip_ge_val256_div_of_no_wrap_of_le
    a0 a1 a2 a3 b0 b1 b2 b3 hb3nz hshift_nz hcall
    hUn21_lt_vTop h_no_wrap h_le

end EvmAsm.Evm64
