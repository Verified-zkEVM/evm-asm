import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge
import EvmAsm.Evm64.DivMod.Spec.CallSkipOverestimateBridge
import EvmAsm.Evm64.EvmWordArith.Div128FinalAssembly
import EvmAsm.Evm64.EvmWordArith.Div128KB6Composition
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- A four-limb value below `2^192` has zero top limb. This packages the
    arithmetic shape needed by later n=1 call-regime side conditions. -/
theorem val256_top_limb_zero_of_lt_pow192
    (x0 x1 x2 x3 : Word)
    (h_lt : val256 x0 x1 x2 x3 < 2^192) :
    x3 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  unfold val256 at h_lt
  have hx3 := x3.isLt
  omega

/-- A four-limb value below one machine word has zero top limb. -/
theorem val256_top_limb_zero_of_lt_word
    (x0 x1 x2 x3 bound : Word)
    (h_lt : val256 x0 x1 x2 x3 < bound.toNat) :
    x3 = 0 := by
  exact val256_top_limb_zero_of_lt_pow192 x0 x1 x2 x3 (by
    have h_bound := bound.isLt
    omega)

/-- A four-limb value below one machine word has zero limb 2. -/
theorem val256_limb2_zero_of_lt_word
    (x0 x1 x2 x3 bound : Word)
    (h_lt : val256 x0 x1 x2 x3 < bound.toNat) :
    x2 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  unfold val256 at h_lt
  have h_bound := bound.isLt
  have hx2 := x2.isLt
  have hx3 := x3.isLt
  omega

/-- A four-limb value below one machine word has zero limb 1. -/
theorem val256_limb1_zero_of_lt_word
    (x0 x1 x2 x3 bound : Word)
    (h_lt : val256 x0 x1 x2 x3 < bound.toNat) :
    x1 = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [show (0 : Word).toNat = 0 from rfl]
  unfold val256 at h_lt
  have h_bound := bound.isLt
  have hx1 := x1.isLt
  have hx2 := x2.isLt
  have hx3 := x3.isLt
  omega

/-- A four-limb value below one machine word has all high limbs zero. -/
theorem val256_high_limbs_zero_of_lt_word
    (x0 x1 x2 x3 bound : Word)
    (h_lt : val256 x0 x1 x2 x3 < bound.toNat) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
  exact ⟨val256_limb1_zero_of_lt_word x0 x1 x2 x3 bound h_lt,
    val256_limb2_zero_of_lt_word x0 x1 x2 x3 bound h_lt,
    val256_top_limb_zero_of_lt_word x0 x1 x2 x3 bound h_lt⟩

/-- Project a one-word bound on the R3 remainder into zero high limbs. -/
theorem fullDivN1R3_high_limbs_zero_of_remainder_lt
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 bound : Word)
    (h_lt :
      val256
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      bound.toNat) :
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 = 0 ∧
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  exact val256_high_limbs_zero_of_lt_word
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    bound h_lt

/-- Project a one-word bound on the R2 remainder into zero high limbs. -/
theorem fullDivN1R2_high_limbs_zero_of_remainder_lt
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 bound : Word)
    (h_lt :
      val256
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      bound.toNat) :
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 = 0 ∧
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  exact val256_high_limbs_zero_of_lt_word
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    bound h_lt

/-- Project a one-word bound on the R1 remainder into zero high limbs. -/
theorem fullDivN1R1_high_limbs_zero_of_remainder_lt
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 bound : Word)
    (h_lt :
      val256
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      bound.toNat) :
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 = 0 ∧
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  exact val256_high_limbs_zero_of_lt_word
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    bound h_lt

/-- First n=1 step carry-zero reducer. For the call branch, the step starts
    with top limb zero, so proving the `mulsubN4` carry `c3` is zero is enough
    to discharge `fullDivN1R3CarryZero`. -/
theorem fullDivN1R3CarryZero_true_of_mulsub_c3_zero
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hc3 :
      mulsubN4_c3
        (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1)
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (0 : Word)
        (0 : Word) = 0) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1R3CarryZero fullDivN1R3
  exact iterN1_true_carry_zero_of_mulsub_c3_zero
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.2
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    (0 : Word)
    (0 : Word)
    (0 : Word)
    hc3 rfl

/-- Product-bound form of the first n=1 step carry-zero reducer. This composes
    the generic `mulsubN4_c3` inequality bridge with the R3 reducer above, so
    later arithmetic only needs to prove that the selected trial quotient times
    the normalized n=1 divisor is bounded by the first partial dividend. -/
theorem fullDivN1R3CarryZero_true_of_qHat_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (h_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        val256
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2 ≤
        val256
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (0 : Word)
          (0 : Word)) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_mulsub_c3_zero
  exact c3_un_zero_of_qHat_mul_le (qHat :=
    div128Quot
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1) h_mul_le

/-- 128/64-bound form of the first n=1 step carry-zero reducer. When the
    normalized divisor is one-limb, the generic product bound for R3 is exactly
    the usual `qHat * v0 ≤ uHi * 2^64 + uLo` obligation. -/
theorem fullDivN1R3CarryZero_true_of_qHat_v0_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hv1z : (fullDivN1NormV b0 b1 b2 b3).2.1 = 0)
    (hv2z : (fullDivN1NormV b0 b1 b2 b3).2.2.1 = 0)
    (hv3z : (fullDivN1NormV b0 b1 b2 b3).2.2.2 = 0)
    (h_qHat_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat ≤
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_qHat_mul_le
  rw [hv1z, hv2z, hv3z]
  simp [EvmWord.val256]
  omega

/-- Generic n=1 call-iteration carry-zero reducer for the one-limb divisor
    shape. An all-phases no-wrap invariant for the selected 128/64 trial call
    gives the tight `div128Quot` product bound; with a zero incoming top limb,
    this is enough to discharge the iteration carry. -/
theorem iterN1_true_carry_zero_of_v0_all_phases_no_wrap
    (v0 u0 u1 u2 u3 uTop : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat * 2^64 + u0.toNat < v0.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv u1 u0 v0)
    (huTop : uTop = 0) :
    (iterN1 true v0 0 0 0 u0 u1 u2 u3 uTop).2.2.2.2.2 = 0 := by
  apply iterN1_true_carry_zero_of_mulsub_c3_zero
  · apply c3_un_zero_of_qHat_mul_le
    have hq_le := div128Quot_le_q_true u1 u0 v0 hv0_norm hcall h_inv
    have h_product :
        (div128Quot u1 u0 v0).toNat * v0.toNat ≤
          u1.toNat * 2^64 + u0.toNat := by
      exact le_trans (Nat.mul_le_mul_right v0.toNat hq_le)
        (Nat.div_mul_le_self (u1.toNat * 2^64 + u0.toNat) v0.toNat)
    simp [EvmWord.val256]
    have hu2 := u2.isLt
    have hu3 := u3.isLt
    omega
  · exact huTop

/-- If a one-limb `mulsubN4` starts from a two-limb partial dividend and has
    zero final carry, the top remainder limb is zero. -/
theorem mulsubN4_top_limb_zero_of_one_limb_c3_zero
    (q v0 u0 u1 : Word)
    (hc3 : (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0) :
    (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.2.1 = 0 := by
  exact val256_top_limb_zero_of_lt_pow192
    (mulsubN4 q v0 0 0 0 u0 u1 0 0).1
    (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.1
    (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.1
    (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.2.1
    (by
      have hmul := mulsubN4_val256_eq q v0 0 0 0 u0 u1 0 0
      dsimp only at hmul
      rw [hc3, show (0 : Word).toNat = 0 from rfl, Nat.zero_mul, Nat.add_zero]
        at hmul
      have hms_le :
          val256 (mulsubN4 q v0 0 0 0 u0 u1 0 0).1
            (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.1
            (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.1
            (mulsubN4 q v0 0 0 0 u0 u1 0 0).2.2.2.1 ≤
          val256 u0 u1 0 0 := by
        nlinarith [hmul]
      have hu0 := u0.isLt
      have hu1 := u1.isLt
      simp [EvmWord.val256] at hms_le ⊢
      omega)

/-- Call-path n=1 structural top-limb reducer for a one-limb divisor and zero
    incoming top limb. -/
theorem iterN1_true_top_limb_zero_of_mulsub_c3_zero
    (v0 u0 u1 : Word)
    (hc3 : mulsubN4_c3 (div128Quot u1 u0 v0) v0 0 0 0 u0 u1 0 0 = 0) :
    (iterN1 true v0 0 0 0 u0 u1 0 0 0).2.2.2.2.1 = 0 := by
  simp only [iterN1_true]
  unfold iterN1Call
  rw [iterWithDoubleAddback_no_borrow]
  · unfold mulsubN4_c3 at hc3
    exact mulsubN4_top_limb_zero_of_one_limb_c3_zero
      (div128Quot u1 u0 v0) v0 u0 u1 hc3
  · unfold mulsubN4_c3 at hc3
    rw [hc3]
    decide

/-- When the n=1 CLZ shift is nonzero, the anti-shift spill from the low
    divisor limb into normalized limb 1 is zero. -/
theorem fullDivN1AntiShift_spill_zero_of_shift_nz
    (b0 : Word)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    b0 >>> ((fullDivN1AntiShift b0).toNat % 64) = 0 := by
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hshift_le : (clzResult b0).1.toNat ≤ 63 := clzResult_fst_toNat_le b0
  have hanti :
      (fullDivN1AntiShift b0).toNat % 64 = 64 - (clzResult b0).1.toNat := by
    unfold fullDivN1AntiShift fullDivN1Shift
    exact antiShift_toNat_mod_eq h_shift_pos hshift_le
  rw [hanti]
  exact (ushiftRight_eq_zero_iff (64 - (clzResult b0).1.toNat)).mpr
    (clzResult_fst_top_bound b0)

/-- Under the runtime n=1 divisor shape and a nonzero normalization shift,
    normalized divisor limb 1 is zero. -/
theorem fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz
    (b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormV b0 b1 b2 b3).2.1 = 0 := by
  rw [fullDivN1NormV_limb1_eq_of_shape b0 b1 b2 b3 hb1z]
  exact fullDivN1AntiShift_spill_zero_of_shift_nz b0 hshift_nz

/-- R2 call-branch n=1 carry-zero reducer from the generic all-phases
    iteration lemma. The remaining arithmetic side conditions are the R3
    top-limb-zero fact, the 128/64 call-regime bound for the selected R2
    partial dividend, and the all-phases no-wrap invariant for that same call. -/
theorem fullDivN1R2CarryZero_true_true_of_shape_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hr3_top_zero :
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hcall :
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1R2CarryZero true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1R2CarryZero fullDivN1R2
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_true_carry_zero_of_v0_all_phases_no_wrap
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hv0_norm hcall h_inv hr3_top_zero

/-- R2 call-branch n=1 carry-zero reducer from a one-word bound on the R3
    remainder. The bound gives the R3 top-limb-zero fact and the strict
    128/64 call-regime inequality for the next step. -/
theorem fullDivN1R2CarryZero_true_true_of_shape_r3_remainder_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hr3_lt :
      val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1R2CarryZero true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h_high :=
    fullDivN1R3_high_limbs_zero_of_remainder_lt true
      a0 a1 a2 a3 b0 b1 b2 b3
      (fullDivN1NormV b0 b1 b2 b3).1 hr3_lt
  have hr3_top_zero :
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 :=
    h_high.2.2
  have hr3_limb0_lt :
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat <
        (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
    rw [h_high.1, h_high.2.1, h_high.2.2] at hr3_lt
    simpa [EvmWord.val256] using hr3_lt
  have hcall :
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64 := by
    have hu2 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.isLt
    omega
  exact fullDivN1R2CarryZero_true_true_of_shape_all_phases_no_wrap
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
    hr3_top_zero hv0_norm hcall h_inv

/-- R1 call-branch n=1 carry-zero reducer from the generic all-phases
    iteration lemma. This mirrors the R2 reducer one step later: the remaining
    arithmetic side conditions are the R2 top-limb-zero fact, the 128/64
    call-regime bound for the selected R1 partial dividend, and the all-phases
    no-wrap invariant for that same call. -/
theorem fullDivN1R1CarryZero_true_true_true_of_shape_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hr2_top_zero :
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hcall :
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1R1CarryZero true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1R1CarryZero fullDivN1R1
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_true_carry_zero_of_v0_all_phases_no_wrap
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hv0_norm hcall h_inv hr2_top_zero

/-- R1 call-branch n=1 carry-zero reducer from a one-word bound on the R2
    remainder. This mirrors the R2 wrapper one step later. -/
theorem fullDivN1R1CarryZero_true_true_true_of_shape_r2_remainder_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hr2_lt :
      val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1R1CarryZero true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h_high :=
    fullDivN1R2_high_limbs_zero_of_remainder_lt true true
      a0 a1 a2 a3 b0 b1 b2 b3
      (fullDivN1NormV b0 b1 b2 b3).1 hr2_lt
  have hr2_top_zero :
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 :=
    h_high.2.2
  have hr2_limb0_lt :
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat <
        (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
    rw [h_high.1, h_high.2.1, h_high.2.2] at hr2_lt
    simpa [EvmWord.val256] using hr2_lt
  have hcall :
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64 := by
    have hu1 := (fullDivN1NormU a0 a1 a2 a3 b0).2.1.isLt
    omega
  exact fullDivN1R1CarryZero_true_true_true_of_shape_all_phases_no_wrap
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
    hr2_top_zero hv0_norm hcall h_inv

/-- Final R0 call-branch n=1 carry-zero reducer from the generic all-phases
    iteration lemma. This completes the same mechanical reduction for the last
    n=1 call step, leaving the R1 top-limb-zero fact, the 128/64 call-regime
    bound, and the all-phases no-wrap invariant explicit. -/
theorem fullDivN1FinalCarryZero_true_true_true_true_of_shape_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hr1_top_zero :
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hcall :
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1FinalCarryZero true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1FinalCarryZero fullDivN1R0
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_true_carry_zero_of_v0_all_phases_no_wrap
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hv0_norm hcall h_inv hr1_top_zero

/-- Final R0 call-branch n=1 carry-zero reducer from a one-word bound on the
    R1 remainder. This completes the same bound-to-carry reduction pattern for
    the last n=1 call step. -/
theorem fullDivN1FinalCarryZero_true_true_true_true_of_shape_r1_remainder_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63)
    (hr1_lt :
      val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1FinalCarryZero true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  have h_high :=
    fullDivN1R1_high_limbs_zero_of_remainder_lt true true true
      a0 a1 a2 a3 b0 b1 b2 b3
      (fullDivN1NormV b0 b1 b2 b3).1 hr1_lt
  have hr1_top_zero :
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 :=
    h_high.2.2
  have hr1_limb0_lt :
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat <
        (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
    rw [h_high.1, h_high.2.1, h_high.2.2] at hr1_lt
    simpa [EvmWord.val256] using hr1_lt
  have hcall :
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat <
          (fullDivN1NormV b0 b1 b2 b3).1.toNat * 2^64 := by
    have hu0 := (fullDivN1NormU a0 a1 a2 a3 b0).1.isLt
    omega
  exact fullDivN1FinalCarryZero_true_true_true_true_of_shape_all_phases_no_wrap
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
    hr1_top_zero hv0_norm hcall h_inv

/-- Runtime n=1 divisor-shape form of the first-step carry-zero reducer. This
    leaves only the standard 128/64 product bound for the selected trial
    quotient. -/
theorem fullDivN1R3CarryZero_true_of_shape_qHat_v0_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (h_qHat_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat ≤
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  exact fullDivN1R3CarryZero_true_of_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz)
    (fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z)
    (fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z)
    h_qHat_mul_le

/-- Runtime n=1 divisor-shape form of the first-step top-limb-zero reducer. -/
theorem fullDivN1R3_top_limb_zero_true_of_shape_qHat_v0_mul_le
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (h_qHat_mul_le :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat ≤
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) :
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  unfold fullDivN1R3
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  apply iterN1_true_top_limb_zero_of_mulsub_c3_zero
  apply c3_un_zero_of_qHat_mul_le
  simp [EvmWord.val256]
  omega

/-- Exact-floor form of the first-step n=1 carry-zero reducer. Once the
    selected `div128Quot` is identified with the usual 128/64 Nat quotient,
    the product bound follows from `Nat.div_mul_le_self`. -/
theorem fullDivN1R3CarryZero_true_of_shape_div128Quot_floor
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (h_qHat_eq :
      (div128Quot
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1).toNat =
        ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) /
          (fullDivN1NormV b0 b1 b2 b3).1.toNat) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  apply fullDivN1R3CarryZero_true_of_shape_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  rw [h_qHat_eq]
  exact Nat.div_mul_le_self
    ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat)
    (fullDivN1NormV b0 b1 b2 b3).1.toNat

/-- The first n=1 128/64 trial call is in the strict call regime. A positive
    normalization shift makes the overflow limb of the normalized dividend
    below `2^63`, while the normalized divisor limb is at least `2^63`. -/
theorem fullDivN1NormU_top_lt_normV_limb0_of_b0_ne_zero_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb0nz : b0 ≠ 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 :
      (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)).toNat <
        2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b0).1 h_shift_pos
      (clzResult_fst_toNat_le b0)
  have h_b0_ge_pow63 :
      (b0 <<< ((clzResult b0).1.toNat % 64)).toNat ≥ 2^63 :=
    b3_shifted_ge_pow63 hb0nz
  have h_lt := Nat.lt_of_lt_of_le h_u4_lt_pow63 h_b0_ge_pow63
  simpa [fullDivN1NormU, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift]
    using h_lt

/-- Runtime n=1 divisor-shape wrapper for the strict first-call regime. -/
theorem fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  exact fullDivN1NormU_top_lt_normV_limb0_of_b0_ne_zero_shift_nz
    a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    hshift_nz

/-- The high half of the normalized n=1 divisor limb satisfies the
    normalization lower bound expected by the 128/64 quotient machinery. -/
theorem fullDivN1NormV_limb0_dHi_ge_pow31_of_b0_ne_zero
    (b0 b1 b2 b3 : Word)
    (hb0nz : b0 ≠ 0) :
    ((fullDivN1NormV b0 b1 b2 b3).1 >>> (32 : BitVec 6).toNat).toNat ≥
      2^31 := by
  apply div128Quot_dHi_ge_pow31
  simpa [fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift] using
    (b3_shifted_ge_pow63 hb0nz)

/-- Runtime n=1 divisor-shape wrapper for the normalized divisor high-half
    lower bound. -/
theorem fullDivN1NormV_limb0_dHi_ge_pow31_of_shape
    (b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    ((fullDivN1NormV b0 b1 b2 b3).1 >>> (32 : BitVec 6).toNat).toNat ≥
      2^31 := by
  exact fullDivN1NormV_limb0_dHi_ge_pow31_of_b0_ne_zero b0 b1 b2 b3
    (fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)

/-- The n=1 normalized divisor top limb is at least `2^63` — the full-strength
    normalization invariant (the `…_dHi_ge_pow31` lemma above is its high-half
    corollary). This is the `vTop ≥ 2^63` precondition of `div128Quot_v5_eq_q_true`
    when specialized to the n=1 first trial call, so the v5 n=1 trial computes the
    exact floor — discharging the n=1 carry-zero (via the
    `…_of_shape_div128Quot_floor` pattern) from shape alone. -/
theorem fullDivN1NormV_limb0_ge_pow63_of_shape
    (b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63 := by
  have hb0nz := fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  have h := b3_shifted_ge_pow63 hb0nz
  simpa [fullDivN1NormV, fullDivN1Shift] using h

/-- **The v5 trial for the n=1 first call is the exact 128/64 floor, from shape.**
    Composes `div128Quot_v5_eq_q_true` (the v5 capped quotient is exact under
    `vTop ≥ 2^63` ∧ `uHi < vTop`) with the n=1 normalization invariants
    `fullDivN1NormV_limb0_ge_pow63_of_shape` and
    `fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz`.

    This is the v5 provider for the `h_qHat_eq` hypothesis of
    `fullDivN1R3CarryZero_true_of_shape_div128Quot_floor`: it discharges the
    n=1 first-trial `div128Quot = floor` UNCONDITIONALLY from shape (which is
    FALSE for v4 `div128Quot` even in the call regime — see
    `ceV4Div128Call_div128Quot_ne_floor`). The exact floor is the true quotient
    digit (single-limb divisor), so the mulsub leaves no borrow → carry-zero
    from shape, sidestepping the false-universal `Carry2NzAll`. -/
theorem fullDivN1R3_div128Quot_v5_eq_floor_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (div128Quot_v5
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormV b0 b1 b2 b3).1).toNat =
      ((fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^64 +
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat) /
        (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  apply div128Quot_v5_eq_q_true
  · exact fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  · exact fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz

/-- The high half of any normalized n=1 divisor limb is a 32-bit quantity. -/
theorem fullDivN1NormV_limb0_dHi_lt_pow32 (b0 b1 b2 b3 : Word) :
    ((fullDivN1NormV b0 b1 b2 b3).1 >>> (32 : BitVec 6).toNat).toNat <
      2^32 := by
  rw [BitVec.toNat_ushiftRight, show (32 : BitVec 6).toNat = 32 by decide,
    Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul (fullDivN1NormV b0 b1 b2 b3).1.isLt

/-- The low half of any normalized n=1 divisor limb is a 32-bit quantity. -/
theorem fullDivN1NormV_limb0_dLo_lt_pow32 (b0 b1 b2 b3 : Word) :
    (((fullDivN1NormV b0 b1 b2 b3).1 <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat < 2^32 := by
  rw [BitVec.toNat_ushiftRight, show (32 : BitVec 6).toNat = 32 by decide,
    Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_of_lt_mul
    ((fullDivN1NormV b0 b1 b2 b3).1 <<< (32 : BitVec 6).toNat).isLt

/-- High/low 32-bit reconstruction for the normalized n=1 divisor limb. -/
theorem fullDivN1NormV_limb0_decomp (b0 b1 b2 b3 : Word) :
    (fullDivN1NormV b0 b1 b2 b3).1.toNat =
      ((fullDivN1NormV b0 b1 b2 b3).1 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      (((fullDivN1NormV b0 b1 b2 b3).1 <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat := by
  exact div128Quot_vTop_decomp (fullDivN1NormV b0 b1 b2 b3).1

/-- Runtime n=1 shape wrapper for the `uHi < dHi*2^32+dLo` precondition used
    by `div128Quot_toNat_eq_strict` on the first R3 trial call. -/
theorem fullDivN1NormU_top_lt_normV_limb0_halves_of_shape_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat <
      ((fullDivN1NormV b0 b1 b2 b3).1 >>> (32 : BitVec 6).toNat).toNat * 2^32 +
      (((fullDivN1NormV b0 b1 b2 b3).1 <<< (32 : BitVec 6).toNat) >>>
        (32 : BitVec 6).toNat).toNat := by
  have hlt := fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
    a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  rwa [fullDivN1NormV_limb0_decomp b0 b1 b2 b3] at hlt

/-- Instantiation of `div128Quot_toNat_eq_strict` for the first n=1 R3 trial
    quotient. The remaining side condition is the usual final low-half quotient
    bound `q0' < 2^32`. -/
theorem fullDivN1R3_div128Quot_toNat_eq_strict_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 →
    (div128Quot uHi uLo vTop).toNat = q1'.toNat * 2^32 + q0'.toNat := by
  intro uHi uLo vTop dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
    hq0
  exact div128Quot_toNat_eq_strict uHi uLo vTop
    (by
      simpa [vTop] using
        fullDivN1NormV_limb0_dHi_ge_pow31_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (by simpa [vTop] using fullDivN1NormV_limb0_dHi_lt_pow32 b0 b1 b2 b3)
    (by simpa [vTop] using fullDivN1NormV_limb0_dLo_lt_pow32 b0 b1 b2 b3)
    (by
      simpa [uHi, vTop] using
        fullDivN1NormU_top_lt_normV_limb0_halves_of_shape_shift_nz
          a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
    hq0

/-- Instantiation of the generic second-half quotient bound for the first n=1
    R3 trial call. This exposes the final semantic `un21 < vTop` precondition
    in the same local names used by
    `fullDivN1R3_div128Quot_toNat_eq_strict_of_shape`. -/
theorem fullDivN1R3_q0_prime_lt_pow32_of_shape_un21_lt
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    un21.toNat < dHi.toNat * 2^32 + dLo.toNat →
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 := by
  intro uHi uLo vTop dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 hun21_lt q0 rhat2 hi2 q0c
    rhat2c q0'
  exact div128Quot_q0_prime_lt_pow32 un21 dHi dLo uLo
    (by
      simpa [vTop, dHi] using
        fullDivN1NormV_limb0_dHi_ge_pow31_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (by simpa [vTop, dHi] using fullDivN1NormV_limb0_dHi_lt_pow32 b0 b1 b2 b3)
    (by simpa [vTop, dLo] using fullDivN1NormV_limb0_dLo_lt_pow32 b0 b1 b2 b3)
    hun21_lt

/-- Instantiation of the R3 second-half quotient bound from the selected
    `Div128PhaseNoWrapInv`. This is the phase-invariant entry point for the
    `q0' < 2^32` subgoal used by the strict R3 quotient expansion. -/
theorem fullDivN1R3_q0_prime_lt_pow32_of_shape_phase_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128PhaseNoWrapInv uHi uLo vTop →
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    q0'.toNat < 2^32 := by
  intro uHi uLo vTop h_inv dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
  exact fullDivN1R3_q0_prime_lt_pow32_of_shape_un21_lt
    a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z
    (Div128PhaseNoWrapInv.un21Lt h_inv)

/-- N1 R3-specific Phase-1 product no-wrap projection from the selected
    `Div128PhaseNoWrapInv`. This names the second Phase-1 conjunct in the
    local R3 trial-call vocabulary. -/
theorem fullDivN1R3_phase1_no_wrap_of_phase_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128PhaseNoWrapInv uHi uLo vTop →
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat := by
  intro uHi uLo vTop h_inv dHi dLo div_un1 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat'
  exact Div128PhaseNoWrapInv.phase1NoWrap h_inv

/-- N1 R3-specific Phase-2 product no-wrap projection from the selected
    `Div128AllPhasesNoWrapInv`. This names the final all-phases conjunct in
    the local R3 trial-call vocabulary. -/
theorem fullDivN1R3_phase2_no_wrap_of_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128AllPhasesNoWrapInv uHi uLo vTop →
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' := if rhat2cHi = 0 then
                    (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat := by
  intro uHi uLo vTop h_inv dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c
    rhat2cHi rhat2Un0 q0' rhat2'
  exact Div128AllPhasesNoWrapInv.phase2NoWrap h_inv

/-- Assemble the selected R3 all-phases no-wrap invariant from the three local
    R3 conjuncts. This is the R3-vocabulary wrapper around
    `Div128AllPhasesNoWrapInv.ofConjuncts`. -/
theorem fullDivN1R3_all_phases_no_wrap_of_conjuncts
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let rhat2cHi := rhat2c >>> (32 : BitVec 6).toNat
    let rhat2Un0 := (rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' := if rhat2cHi = 0 then
                    (if BitVec.ult rhat2Un0 (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    un21.toNat < dHi.toNat * 2^32 + dLo.toNat →
    q1'.toNat * dLo.toNat ≤ (rhat'.toNat % 2^32) * 2^32 + div_un1.toNat →
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat →
    Div128AllPhasesNoWrapInv uHi uLo vTop := by
  intro uHi uLo vTop dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c
    rhat2c rhat2cHi rhat2Un0 q0' rhat2' h_un21 h_phase1 h_phase2
  exact Div128AllPhasesNoWrapInv.ofConjuncts h_un21 h_phase1 h_phase2

/-- Strict first n=1 R3 trial quotient expansion under the generic
    `Div128PhaseNoWrapInv` for the selected 128/64 call. This packages the
    local `un21 < vTop` extraction and the `q0' < 2^32` reducer into the
    strict `div128Quot` equality used by the product-bound path. -/
theorem fullDivN1R3_div128Quot_toNat_eq_strict_of_shape_phase_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128PhaseNoWrapInv uHi uLo vTop →
    let dHi := vTop >>> (32 : BitVec 6).toNat
    let dLo := (vTop <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := uLo >>> (32 : BitVec 6).toNat
    let div_un0 := (uLo <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu uHi dHi
    let rhat := uHi - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let cu_rhat_un1 := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    (div128Quot uHi uLo vTop).toNat = q1'.toNat * 2^32 + q0'.toNat := by
  intro uHi uLo vTop h_inv dHi dLo div_un1 div_un0 q1 rhat hi1 q1c rhatc qDlo
    rhatUn1 q1' rhat' cu_rhat_un1 cu_q1_dlo un21 q0 rhat2 hi2 q0c rhat2c q0'
  have hq0 : q0'.toNat < 2^32 :=
    fullDivN1R3_q0_prime_lt_pow32_of_shape_phase_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z h_inv
  exact div128Quot_toNat_eq_strict uHi uLo vTop
    (by
      simpa [vTop] using
        fullDivN1NormV_limb0_dHi_ge_pow31_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (by simpa [vTop] using fullDivN1NormV_limb0_dHi_lt_pow32 b0 b1 b2 b3)
    (by simpa [vTop] using fullDivN1NormV_limb0_dLo_lt_pow32 b0 b1 b2 b3)
    (by
      simpa [uHi, vTop] using
        fullDivN1NormU_top_lt_normV_limb0_halves_of_shape_shift_nz
          a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
    hq0

/-- All-phases no-wrap form of the first-step n=1 carry-zero reducer. The
    strict div128 KB-6 bound gives `qHat ≤ floor((uHi: uLo) / vTop)`, which is
    enough to discharge the R3 product bound and hence the `mulsubN4` carry. -/
theorem fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128AllPhasesNoWrapInv uHi uLo vTop →
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 := by
  intro uHi uLo vTop h_inv
  apply fullDivN1R3CarryZero_true_of_shape_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  have hb0nz : b0 ≠ 0 :=
    fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  have hvTop_norm : vTop.toNat ≥ 2^63 := by
    simpa [vTop, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift] using
      (b3_shifted_ge_pow63 hb0nz)
  have h_uHi_lt :
      uHi.toNat < vTop.toNat := by
    simpa [uHi, vTop] using
      fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := by
    have huLo := uLo.isLt
    omega
  have hq_le :=
    div128Quot_le_q_true uHi uLo vTop hvTop_norm hcall h_inv
  have h_qHat_mul_le :
      (div128Quot uHi uLo vTop).toNat * vTop.toNat ≤
        uHi.toNat * 2^64 + uLo.toNat := by
    exact le_trans (Nat.mul_le_mul_right vTop.toNat hq_le)
      (Nat.div_mul_le_self (uHi.toNat * 2^64 + uLo.toNat) vTop.toNat)
  simpa [uHi, uLo, vTop] using h_qHat_mul_le

/-- Bundle the n=1 all-call carry-zero reducers behind the concrete
    one-word remainder bounds for the first three steps. -/
theorem fullDivN1CarryZeros_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hr3_lt :
      val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr2_lt :
      val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr1_lt :
      val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv_r3 : Div128AllPhasesNoWrapInv
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r2 : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r1 : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_final : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1R3CarryZero true a0 a1 a2 a3 b0 b1 b2 b3 ∧
      fullDivN1R2CarryZero true true a0 a1 a2 a3 b0 b1 b2 b3 ∧
      fullDivN1R1CarryZero true true true a0 a1 a2 a3 b0 b1 b2 b3 ∧
      fullDivN1FinalCarryZero true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hb0nz : b0 ≠ 0 :=
    fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  have hv0_norm : (fullDivN1NormV b0 b1 b2 b3).1.toNat ≥ 2^63 := by
    simpa [fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift] using
      (b3_shifted_ge_pow63 hb0nz)
  refine ⟨?hr3, ?hr2, ?hr1, ?hfinal⟩
  · exact fullDivN1R3CarryZero_true_of_shape_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz h_inv_r3
  · exact fullDivN1R2CarryZero_true_true_of_shape_r3_remainder_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
      hv0_norm hr3_lt h_inv_r2
  · exact fullDivN1R1CarryZero_true_true_true_of_shape_r2_remainder_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
      hv0_norm hr2_lt h_inv_r1
  · exact fullDivN1FinalCarryZero_true_true_true_true_of_shape_r1_remainder_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
      hv0_norm hr1_lt h_inv_final

/-- The all-call carry-zero package is enough to discharge the normalized
    n=1 Euclidean equation for the all-true branch path. -/
theorem fullDivN1NormalizedMulSubEq_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_lt :
      val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr2_lt :
      val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr1_lt :
      val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv_r3 : Div128AllPhasesNoWrapInv
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r2 : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r1 : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_final : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1) :
    fullDivN1NormalizedMulSubEq true true true true
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  obtain ⟨hr3_zero, hr2_zero, hr1_zero, hfinal_zero⟩ :=
    fullDivN1CarryZeros_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
      hr3_lt hr2_lt hr1_lt h_inv_r3 h_inv_r2 h_inv_r1 h_inv_final
  exact fullDivN1NormalizedMulSubEq_of_raw_step_conservation
    true true true true a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- All-call n=1 reducer for the legacy quotient-overestimate surface. The
    normalized final-remainder bound supplies the usual quotient comparison
    once the all-carry package has produced the normalized Euclidean equation. -/
theorem fullDivN1QuotientOverestimate_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_lt :
      val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr2_lt :
      val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr1_lt :
      val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv_r3 : Div128AllPhasesNoWrapInv
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r2 : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r1 : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_final : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1QuotientOverestimate true true true true
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hmulsub :=
    fullDivN1NormalizedMulSubEq_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_lt hr2_lt hr1_lt h_inv_r3 h_inv_r2 h_inv_r1 h_inv_final
  exact fullDivN1QuotientOverestimate_of_normalized_mulsub_remainder_lt
    true true true true hmulsub hrem_lt

/-- All-call n=1 quotient-word reducer from one-word step remainder bounds,
    all-phases no-wrap invariants, and the normalized final-remainder bound. -/
theorem fullDivN1QuotientWord_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_lt :
      val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr2_lt :
      val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (hr1_lt :
      val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (h_inv_r3 : Div128AllPhasesNoWrapInv
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r2 : Div128AllPhasesNoWrapInv
      (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_r1 : Div128AllPhasesNoWrapInv
      (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (h_inv_final : Div128AllPhasesNoWrapInv
      (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hrem_lt : fullDivN1NormalizedRemainderLt true true true true
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1QuotientWord true true true true
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have hmulsub :=
    fullDivN1NormalizedMulSubEq_true_true_true_true_of_shape_remainders_lt_all_phases_no_wrap
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz hcarry2
      hr3_lt hr2_lt hr1_lt h_inv_r3 h_inv_r2 h_inv_r1 h_inv_final
  exact fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
    true true true true hbnz hmulsub hrem_lt

/-- All-phases no-wrap form of the first-step n=1 top-limb-zero reducer. -/
theorem fullDivN1R3_top_limb_zero_true_of_shape_all_phases_no_wrap
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    let uHi := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    let uLo := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    let vTop := (fullDivN1NormV b0 b1 b2 b3).1
    Div128AllPhasesNoWrapInv uHi uLo vTop →
    (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  intro uHi uLo vTop h_inv
  apply fullDivN1R3_top_limb_zero_true_of_shape_qHat_v0_mul_le
    a0 a1 a2 a3 b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  have hb0nz : b0 ≠ 0 :=
    fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z
  have hvTop_norm : vTop.toNat ≥ 2^63 := by
    simpa [vTop, fullDivN1NormV, fullDivN1Shift, fullDivN1AntiShift] using
      (b3_shifted_ge_pow63 hb0nz)
  have h_uHi_lt :
      uHi.toNat < vTop.toNat := by
    simpa [uHi, vTop] using
      fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hcall : uHi.toNat * 2^64 + uLo.toNat < vTop.toNat * 2^64 := by
    have huLo := uLo.isLt
    omega
  have hq_le :=
    div128Quot_le_q_true uHi uLo vTop hvTop_norm hcall h_inv
  have h_qHat_mul_le :
      (div128Quot uHi uLo vTop).toNat * vTop.toNat ≤
        uHi.toNat * 2^64 + uLo.toNat := by
    exact le_trans (Nat.mul_le_mul_right vTop.toNat hq_le)
      (Nat.div_mul_le_self (uHi.toNat * 2^64 + uLo.toNat) vTop.toNat)
  simpa [uHi, uLo, vTop] using h_qHat_mul_le

end EvmAsm.Evm64
