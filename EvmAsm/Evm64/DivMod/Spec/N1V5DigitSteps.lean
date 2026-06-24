/-
  EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps

  The remaining v5 n=1 schoolbook digit steps (R2, R1, R0): carry-zero and
  remainder `< v0`, each discharged from shape with NO `Carry2NzAll` / NO
  `Div128AllPhasesNoWrapInv`.

  Every step is a mechanical instantiation of the abstract helpers
  `iterN1V5_true_{carry_zero,remainder_lt}_of_v0_norm_call`
  (`N1V5CarryZero.lean`): the previous digit's remainder-lt zeroes the incoming
  high limbs (`val256_high_limbs_zero_of_lt_word`) and pins the next digit's
  call regime (`uHi < v0`), so the v5-exact (`div128Quot_v5 = floor`) single-limb
  mulsub neither borrows (carry = 0) nor overflows the remainder (`< v0`).
  Bead evm-asm-wbc4i.9.1.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5CarryZero

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Shared reduction: from a digit's remainder-lt, extract the high-limb-zero
    facts and the `uHi < v0` call regime for the next digit. -/
private theorem n1v5_step_facts
    {x0 x1 x2 x3 v0 : Word}
    (hrem : EvmWord.val256 x0 x1 x2 x3 < v0.toNat) :
    x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ x0.toNat < v0.toNat := by
  obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 v0 hrem
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h2, h3] at hrem
  simpa [EvmWord.val256] using hrem

-- ============================================================================
-- R2
-- ============================================================================

theorem fullDivN1R2V5_carry_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  obtain ⟨h1, h2, h3, hr3lt⟩ := n1v5_step_facts
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R2V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_carry_zero_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr3lt

theorem fullDivN1R2V5_remainder_lt_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  obtain ⟨h1, h2, h3, hr3lt⟩ := n1v5_step_facts
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R2V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr3lt

-- ============================================================================
-- R1
-- ============================================================================

theorem fullDivN1R1V5_carry_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  obtain ⟨h1, h2, h3, hr2lt⟩ := n1v5_step_facts
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R1V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_carry_zero_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr2lt

theorem fullDivN1R1V5_remainder_lt_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  obtain ⟨h1, h2, h3, hr2lt⟩ := n1v5_step_facts
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R1V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr2lt

-- ============================================================================
-- R0
-- ============================================================================

theorem fullDivN1R0V5_carry_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0 := by
  obtain ⟨h1, h2, h3, hr1lt⟩ := n1v5_step_facts
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R0V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_carry_zero_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr1lt

theorem fullDivN1R0V5_remainder_lt_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat := by
  obtain ⟨h1, h2, h3, hr1lt⟩ := n1v5_step_facts
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R0V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr1lt

-- ============================================================================
-- Per-digit quotient extraction (R2, R1, R0): stored digit = `div128Quot_v5`
-- ============================================================================

/-- **v5 n=1 second-digit quotient, from shape.** -/
theorem fullDivN1R2V5_quot_eq_div128_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr3lt⟩ := n1v5_step_facts
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R2V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_quot_eq_div128_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr3lt

/-- **v5 n=1 third-digit quotient, from shape.** -/
theorem fullDivN1R1V5_quot_eq_div128_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr2lt⟩ := n1v5_step_facts
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R1V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_quot_eq_div128_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr2lt

/-- **v5 n=1 fourth-digit quotient, from shape.** -/
theorem fullDivN1R0V5_quot_eq_div128_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      div128Quot_v5 (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                    (fullDivN1NormU a0 a1 a2 a3 b0).1
                    (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr1lt⟩ := n1v5_step_facts
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R0V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_quot_eq_div128_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr1lt

-- ============================================================================
-- Per-digit remainder extraction (R2, R1, R0): stored limb = `uLo -₆₄ q·v0'`
-- ============================================================================

/-- **v5 n=1 second-digit remainder, closed form, from shape.** -/
theorem fullDivN1R2V5_rem_eq_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 =
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1 -
        div128Quot_v5 (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
                      (fullDivN1NormV b0 b1 b2 b3).1 *
          (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr3lt⟩ := n1v5_step_facts
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R2V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_rem_eq_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr3lt

/-- **v5 n=1 third-digit remainder, closed form, from shape.** -/
theorem fullDivN1R1V5_rem_eq_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 =
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1 -
        div128Quot_v5 (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
                      (fullDivN1NormV b0 b1 b2 b3).1 *
          (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr2lt⟩ := n1v5_step_facts
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R1V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_rem_eq_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr2lt

/-- **v5 n=1 fourth-digit remainder, closed form, from shape.** -/
theorem fullDivN1R0V5_rem_eq_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 =
      (fullDivN1NormU a0 a1 a2 a3 b0).1 -
        div128Quot_v5 (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
                      (fullDivN1NormU a0 a1 a2 a3 b0).1
                      (fullDivN1NormV b0 b1 b2 b3).1 *
          (fullDivN1NormV b0 b1 b2 b3).1 := by
  obtain ⟨h1, h2, h3, hr1lt⟩ := n1v5_step_facts
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R0V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_rem_eq_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr1lt

-- ============================================================================
-- Per-step Euclidean conservation (building block for the 4-digit accumulation)
-- ============================================================================

/-- **Abstract per-step v5 Euclidean conservation.** For a normalized one-limb
    divisor in the call regime, `val256(window) = qHat·v0 + val256(remainder)`,
    where `qHat = R.1` is the iteration's quotient digit. From carry=0
    (no-borrow) + `mulsubN4_val256_eq` — NO `Carry2NzAll`. The per-step input to
    the version-agnostic 4-digit accumulation
    (`fullDivN1_four_step_conservation_nat`) yielding the full normalized
    Euclidean equation `fullDivN1NormalizedConservation`. -/
theorem iterN1V5_true_conservation_of_v0_norm_call
    (v0 u0 u1 : Word)
    (hv0_norm : v0.toNat ≥ 2^63)
    (hcall : u1.toNat < v0.toNat) :
    EvmWord.val256 u0 u1 0 0 =
      (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).1.toNat * v0.toNat +
      EvmWord.val256
        (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.1
        (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.1
        (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.1
        (iterN1V5 true v0 0 0 0 u0 u1 0 0 0).2.2.2.2.1 := by
  have hc3 : (mulsubN4 (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0).2.2.2.2 = 0 := by
    apply c3_un_zero_of_qHat_mul_le
    have h_prod : (div128Quot_v5 u1 u0 v0).toNat * v0.toNat ≤ u1.toNat * 2^64 + u0.toNat :=
      le_trans (Nat.mul_le_mul_right v0.toNat
        (div128Quot_v5_le_q_true u1 u0 v0 hv0_norm hcall)) (Nat.div_mul_le_self _ _)
    simp [EvmWord.val256]; omega
  rw [iterN1V5_true]
  unfold iterN1Call_v5
  rw [iterWithDoubleAddback_no_borrow (by rw [hc3]; simp [BitVec.ult])]
  dsimp only
  have hval := mulsubN4_val256_eq (div128Quot_v5 u1 u0 v0) v0 0 0 0 u0 u1 0 0
  simp only [hc3] at hval
  simp [EvmWord.val256] at hval ⊢
  omega

-- ============================================================================
-- Per-digit conservation instantiations (the 4 `hiter` inputs to the
-- version-agnostic `fullDivN1_four_step_conservation_nat` accumulation)
-- ============================================================================

theorem fullDivN1R3V5_conservation_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2 0 0 =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat +
      EvmWord.val256
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  unfold fullDivN1R3V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1V5_true_conservation_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormU_top_lt_normV_limb0_of_shape_shift_nz
      a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)

theorem fullDivN1R2V5_conservation_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1 0 0 =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat +
      EvmWord.val256
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨h1, h2, h3, hr3lt⟩ := n1v5_step_facts
    (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R2V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_conservation_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr3lt

theorem fullDivN1R1V5_conservation_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 0 0 =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat +
      EvmWord.val256
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨h1, h2, h3, hr2lt⟩ := n1v5_step_facts
    (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R1V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_conservation_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr2lt

theorem fullDivN1R0V5_conservation_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 0 0 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat *
        (fullDivN1NormV b0 b1 b2 b3).1.toNat +
      EvmWord.val256
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 := by
  obtain ⟨h1, h2, h3, hr1lt⟩ := n1v5_step_facts
    (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullDivN1R0V5
  simp only [
    fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
    fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
    fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z, h1, h2, h3]
  exact iterN1V5_true_conservation_of_v0_norm_call _ _ _
    (fullDivN1NormV_limb0_ge_pow63_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z) hr1lt

end EvmAsm.Evm64
