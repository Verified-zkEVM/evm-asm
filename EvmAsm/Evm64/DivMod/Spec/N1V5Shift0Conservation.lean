/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Conservation

  Per-digit conservation (`val256 in = q·b0 + val256 remainder`) and the final
  remainder bound for the v5 n=1 **shift=0** loop, at `v = (b0,0,0,0)`,
  `u0 = a3`, `u1=u2=u3=uTop=0`, `u0_orig_{2,1,0} = a2,a1,a0`.

  Each digit's remainder is single-limb (`val256 < b0 < 2^64` ⇒ high limbs 0), so
  the generic single-limb cores (`iterN1V5_true_conservation_of_v0_norm_call`,
  `iterN1V5_true_remainder_lt_of_v0_norm_call`) apply at every digit through
  `fullN1S2/S1/S0`.  Shift=0 counterpart of the conservation/remainder lemmas in
  `N1V5DigitSteps`; together they feed the shift=0 quotient-correctness proof
  (`fullDivN1QuotientWordShift0V5 = EvmWord.div a b`).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps
import EvmAsm.Evm64.DivMod.Spec.N1V5LaneHborrow
import EvmAsm.Evm64.DivMod.LoopIterN1.N1V5IterChainShared
import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

private theorem b0_norm {b0 : Word} (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    b0.toNat ≥ 2 ^ 63 := by
  have h := b3_shifted_ge_pow63 hb0nz
  rw [hclz] at h
  simpa using h

private theorem b0_pos {b0 : Word} (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    (0 : Word).toNat < b0.toNat := by
  have := b0_norm hb0nz hclz
  have hz : (0 : Word).toNat = 0 := by decide
  omega

-- Remainder `val256 < b0` for each digit (shift=0 inputs). --------------------

theorem s3_rem_lt_shift0 (a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.2.1 < b0.toNat := by
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 (b0_norm hb0nz hclz) (b0_pos hb0nz hclz)

theorem s2_rem_lt_shift0 (a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.2.1 < b0.toNat := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s3_rem_lt_shift0 a3 b0 hb0nz hclz)
  unfold fullN1S2
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a2 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s3_rem_lt_shift0 a3 b0 hb0nz hclz))

theorem s1_rem_lt_shift0 (a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.2.1 < b0.toNat := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  unfold fullN1S1
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a1 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz))

theorem s0_rem_lt_shift0 (a0 a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1 < b0.toNat := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  unfold fullN1S0
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_remainder_lt_of_v0_norm_call b0 a0 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz))

-- Per-digit conservation (shift=0 inputs). ------------------------------------

theorem s3_cons_shift0 (a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256 a3 0 0 0 =
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1.toNat * b0.toNat +
      val256
        (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1
        (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.1
        (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.1
        (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.2.2.2.1 := by
  rw [← iterN1V5_true]
  exact iterN1V5_true_conservation_of_v0_norm_call b0 a3 0 (b0_norm hb0nz hclz) (b0_pos hb0nz hclz)

theorem s2_cons_shift0 (a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256 a2 (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1 0 0 =
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1.toNat * b0.toNat +
      val256
        (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1
        (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.1
        (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.1
        (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s3_rem_lt_shift0 a3 b0 hb0nz hclz)
  unfold fullN1S2
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_conservation_of_v0_norm_call b0 a2 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s3_rem_lt_shift0 a3 b0 hb0nz hclz))

theorem s1_cons_shift0 (a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256 a1 (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1 0 0 =
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1.toNat * b0.toNat +
      val256
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.1
        (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  unfold fullN1S1
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_conservation_of_v0_norm_call b0 a1 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz))

theorem s0_cons_shift0 (a0 a1 a2 a3 b0 : Word) (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    val256 a0 (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 0 0 =
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1.toNat * b0.toNat +
      val256
        (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1
        (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1
        (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1
        (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1 := by
  obtain ⟨hz1, hz2, hz3⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ _ (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  unfold fullN1S0
  simp only [hz1, hz2, hz3]
  rw [← iterN1V5_true]
  exact iterN1V5_true_conservation_of_v0_norm_call b0 a0 _ (b0_norm hb0nz hclz)
    (n1v5_limb0_toNat_lt_of_val256_lt (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz))

end EvmAsm.Evm64
