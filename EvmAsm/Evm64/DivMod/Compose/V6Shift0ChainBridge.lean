/-
  EvmAsm.Evm64.DivMod.Compose.V6Shift0ChainBridge

  The shift=0 counterpart of `V6ChainModelBridge` / `V6BodyModelBridge`: when the
  divisor is already normalized (`(clzResult b0).1 = 0`, i.e. `b0 ≥ 2^63`), the
  fast-path body's copyAU lane runs the digit chain on the *un-normalized* window
  `(0, a3, a2, a1, a0)` with divisor `v6nD b0 = b0`.  The division model for this
  lane is `fullDivN1QuotientWordShift0V5` (digits `iterN1Call_v5 b0 … a3` /
  `fullN1S{2,1,0}`), whose correctness `fullDivN1QuotientWordShift0V5_eq_div_of_shape`
  is already proven.

  Each digit reuses the same abstract single-limb facts as the shiftNz lane
  (`iterN1V5_true_{quot_eq_div128,rem_eq}_of_v0_norm_call`), instantiated at the
  shift=0 call regime (`b0 ≥ 2^63`, threaded remainder `< b0`).  The `fullN1S`
  nesting is handled by zeroing the previous digit's high remainder limbs via the
  `s{3,2,1}_rem_lt_shift0` bounds.  Capstone: the body's stored quotient word
  `= EvmWord.div a b`.  Bead `evm-asm-dr466.2` (shift0 lane).
-/

import EvmAsm.Evm64.DivMod.Compose.V6BodyModelBridge
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Quotient
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Bounds
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Conservation
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0QuotientCorrect

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- On the shift=0 branch the normalized divisor limb is just `b0`. -/
theorem v6nD_eq_self_shift0 (b0 : Word) (hclz : (clzResult b0).1 = 0) : v6nD b0 = b0 := by
  unfold v6nD; rw [hclz]; simp

variable (a0 a1 a2 a3 b0 : Word)

-- The shift=0 call regime: `b0 ≥ 2^63` and `0 < b0`.
private theorem s0_norm (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    b0.toNat ≥ 2^63 := b0_ge_pow63_of_clz_zero b0 hb0nz hclz

private theorem s0_zero_lt (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    (0 : Word).toNat < b0.toNat := by
  have := b0_ge_pow63_of_clz_zero b0 hb0nz hclz; simp; omega

-- ============================================================================
-- Digit 3 (top): direct, reusing the abstract single-limb facts.
-- ============================================================================

theorem v6chainQ3_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainQ3 0 a3 b0 = (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1 := by
  rw [v6chainQ3, div128V5CodeQuot_eq_div128Quot_v5, ← iterN1V5_true]
  exact (iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a3 0
    (s0_norm b0 hb0nz hclz) (s0_zero_lt b0 hb0nz hclz)).symm

theorem v6chainR3_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainR3 0 a3 b0 = (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1 := by
  rw [v6chainR3, v6chainQ3, div128V5CodeQuot_eq_div128Quot_v5, ← iterN1V5_true]
  exact (iterN1V5_true_rem_eq_of_v0_norm_call b0 a3 0
    (s0_norm b0 hb0nz hclz) (s0_zero_lt b0 hb0nz hclz)).symm

-- ============================================================================
-- Digit 2: thread digit 3's remainder, zeroing its high limbs.
-- ============================================================================

theorem v6chainQ2_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainQ2 0 a3 a2 b0 = (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1 := by
  have hnorm := s0_norm b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 hnorm (s0_zero_lt b0 hb0nz hclz))
  have hcall2 : (iterN1V5 true b0 0 0 0 a3 0 0 0 0).2.1.toNat < b0.toNat := by
    have h := iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 hnorm (s0_zero_lt b0 hb0nz hclz)
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainQ2, v6chainR3_shift0_eq_model a3 b0 hb0nz hclz,
      div128V5CodeQuot_eq_div128Quot_v5, ← iterN1V5_true]
  unfold fullN1S2
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a2 _ hnorm hcall2]

theorem v6chainR2_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainR2 0 a3 a2 b0 = (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1 := by
  have hnorm := s0_norm b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 hnorm (s0_zero_lt b0 hb0nz hclz))
  have hcall2 : (iterN1V5 true b0 0 0 0 a3 0 0 0 0).2.1.toNat < b0.toNat := by
    have h := iterN1V5_true_remainder_lt_of_v0_norm_call b0 a3 0 hnorm (s0_zero_lt b0 hb0nz hclz)
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainR2, v6chainQ2_shift0_eq_model a2 a3 b0 hb0nz hclz]
  unfold fullN1S2
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a2 _ hnorm hcall2,
      iterN1V5_true_rem_eq_of_v0_norm_call b0 a2 _ hnorm hcall2]

-- ============================================================================
-- Digit 1: thread digit 2's remainder (`fullN1S2`), zeroing its high limbs.
-- ============================================================================

theorem v6chainQ1_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainQ1 0 a3 a2 a1 b0 = (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1 := by
  have hnorm := s0_norm b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  have hcall1 : (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1.toNat < b0.toNat := by
    have h := s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainQ1, v6chainR2_shift0_eq_model a2 a3 b0 hb0nz hclz,
      div128V5CodeQuot_eq_div128Quot_v5]
  unfold fullN1S1
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a1 _ hnorm hcall1]

theorem v6chainR1_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainR1 0 a3 a2 a1 b0 = (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1 := by
  have hnorm := s0_norm b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  have hcall1 : (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1.toNat < b0.toNat := by
    have h := s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainR1, v6chainQ1_shift0_eq_model a1 a2 a3 b0 hb0nz hclz]
  unfold fullN1S1
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a1 _ hnorm hcall1,
      iterN1V5_true_rem_eq_of_v0_norm_call b0 a1 _ hnorm hcall1]

-- ============================================================================
-- Digit 0: thread digit 1's remainder (`fullN1S1`), zeroing its high limbs.
-- ============================================================================

theorem v6chainQ0_shift0_eq_model (hb0nz : b0 ≠ 0) (hclz : (clzResult b0).1 = 0) :
    v6chainQ0 0 a3 a2 a1 a0 b0 = (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1 := by
  have hnorm := s0_norm b0 hb0nz hclz
  obtain ⟨hz2, hz3, hz4⟩ := val256_high_limbs_zero_of_lt_word _ _ _ _ b0
    (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  have hcall0 : (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1.toNat < b0.toNat := by
    have h := s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz
    rw [hz2, hz3, hz4] at h; simpa [val256] using h
  rw [v6chainQ0, v6chainR1_shift0_eq_model a1 a2 a3 b0 hb0nz hclz,
      div128V5CodeQuot_eq_div128Quot_v5]
  unfold fullN1S0
  simp only [← iterN1V5_true]
  rw [hz2, hz3, hz4, iterN1V5_true_quot_eq_div128_of_v0_norm_call b0 a0 _ hnorm hcall0]

-- ============================================================================
-- Capstone: the shift=0 body-window quotient word = `EvmWord.div a b`.
-- ============================================================================

/-- **v6 DIV fast-path shift=0 quotient correctness, from shape.** When the
    divisor is already normalized, the four quotient digits the body stores
    (`v6chainQ_j (0, a3, a2, a1, a0, v6nD b0)`) assemble into `EvmWord.div a b`.
    Composes the shift=0 digit bridges with
    `fullDivN1QuotientWordShift0V5_eq_div_of_shape`. -/
theorem v6n_quotient_word_shift0_eq_div (b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => v6chainQ0 0 a3 a2 a1 a0 (v6nD b0)
      | 1 => v6chainQ1 0 a3 a2 a1 (v6nD b0)
      | 2 => v6chainQ2 0 a3 a2 (v6nD b0)
      | 3 => v6chainQ3 0 a3 (v6nD b0)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have hb0nz : b0 ≠ 0 := by rw [hb1z, hb2z, hb3z] at hbnz; simpa using hbnz
  rw [v6nD_eq_self_shift0 b0 hclz,
      v6chainQ0_shift0_eq_model a0 a1 a2 a3 b0 hb0nz hclz,
      v6chainQ1_shift0_eq_model a1 a2 a3 b0 hb0nz hclz,
      v6chainQ2_shift0_eq_model a2 a3 b0 hb0nz hclz,
      v6chainQ3_shift0_eq_model a3 b0 hb0nz hclz]
  exact fullDivN1QuotientWordShift0V5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hclz

-- ============================================================================
-- Per-limb form: `(EvmWord.div a b).getLimbN j = q[j]` (shift=0 lane).
-- ============================================================================

/-- Shift=0 stored quotient limb `q[0]` is `EvmWord.div`'s limb 0. -/
theorem v6n_div_getLimbN_shift0_0 (b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = v6chainQ0 0 a3 a2 a1 a0 (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 0)
    (v6n_quotient_word_shift0_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)).symm).trans
    EvmWord.getLimbN_fromLimbs_0

/-- Shift=0 stored quotient limb `q[1]` is `EvmWord.div`'s limb 1. -/
theorem v6n_div_getLimbN_shift0_1 (b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1
      = v6chainQ1 0 a3 a2 a1 (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 1)
    (v6n_quotient_word_shift0_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)).symm).trans
    EvmWord.getLimbN_fromLimbs_1

/-- Shift=0 stored quotient limb `q[2]` is `EvmWord.div`'s limb 2. -/
theorem v6n_div_getLimbN_shift0_2 (b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2
      = v6chainQ2 0 a3 a2 (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 2)
    (v6n_quotient_word_shift0_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)).symm).trans
    EvmWord.getLimbN_fromLimbs_2

/-- Shift=0 stored quotient limb `q[3]` is `EvmWord.div`'s limb 3. -/
theorem v6n_div_getLimbN_shift0_3 (b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3
      = v6chainQ3 0 a3 (v6nD b0) := by
  exact ((congrArg (fun w => w.getLimbN 3)
    (v6n_quotient_word_shift0_eq_div a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hclz)).symm).trans
    EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
