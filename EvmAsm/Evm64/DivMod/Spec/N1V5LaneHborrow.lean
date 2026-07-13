/-
  EvmAsm.Evm64.DivMod.Spec.N1V5LaneHborrow

  The four per-digit no-borrow facts for the v5 n=1 lane, discharged from the
  divisor shape.  In the n=1 normalized call regime each digit's single-limb
  mulsub leaves no borrow (the v5 trial is the exact floor), so the loop always
  takes the skip path.  These are exactly the `hborrow_3/2/1/0` hypotheses of
  `divK_loop_n1_call_unified_v5` (instantiated at the normalized inputs), reduced
  to `mulsubN4NoBorrow_div128Quot_v5_of_norm_call`.  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps
import EvmAsm.Evm64.DivMod.Spec.N1V5QuotNoBorrowShared

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Nat-version of the limb0 bound: a remainder whose `val256 < v0` has its low
    limb's `toNat < v0.toNat` (the high limbs vanish). -/
theorem n1v5_limb0_toNat_lt_of_val256_lt {x0 x1 x2 x3 v0 : Word}
    (h : EvmWord.val256 x0 x1 x2 x3 < v0.toNat) : x0.toNat < v0.toNat := by
  obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 v0 h
  have hval : EvmWord.val256 x0 x1 x2 x3 = x0.toNat := by rw [h1, h2, h3]; simp [EvmWord.val256]
  omega

/-- n=1 lane, j=3 (top digit) no-borrow. -/
theorem n1v5_lane_hborrow_3_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormV b0 b1 b2 b3).1)
      (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 0 := by
  rw [fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
      fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
      fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z,
      divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call _ _ _ 0
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

/-- n=1 lane, j=2 no-borrow. -/
theorem n1v5_lane_hborrow_2_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 (fullDivN1NormV b0 b1 b2 b3).1)
      (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  rw [hz1, hz2, hz3,
      fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
      fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
      fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z,
      divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call _ _ _ 0
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (n1v5_limb0_toNat_lt_of_val256_lt
      (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz))

/-- n=1 lane, j=1 no-borrow. -/
theorem n1v5_lane_hborrow_1_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1 (fullDivN1NormV b0 b1 b2 b3).1)
      (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  rw [hz1, hz2, hz3,
      fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
      fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
      fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z,
      divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call _ _ _ 0
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (n1v5_limb0_toNat_lt_of_val256_lt
      (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz))

/-- n=1 lane, j=0 no-borrow. -/
theorem n1v5_lane_hborrow_0_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    mulsubN4NoBorrow
      (divKTrialCallV5QHat (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).1 (fullDivN1NormV b0 b1 b2 b3).1)
      (fullDivN1NormV b0 b1 b2 b3).1 (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1 (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  rw [hz1, hz2, hz3,
      fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
      fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
      fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z,
      divKTrialCallV5QHat_eq_div128Quot_v5]
  exact mulsubN4NoBorrow_div128Quot_v5_of_norm_call _ _ _ 0
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (n1v5_limb0_toNat_lt_of_val256_lt
      (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz))

end EvmAsm.Evm64
