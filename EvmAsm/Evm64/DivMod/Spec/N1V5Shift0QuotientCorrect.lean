/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0QuotientCorrect

  v5 n=1 **shift=0** quotient correctness: the shift=0 schoolbook computes the
  exact quotient `EvmWord.div a b`, from the divisor shape `(clzResult b0).1 = 0`
  (single-limb divisor, already top-bit aligned).

  Shift=0 counterpart of `fullDivN1QuotientWordV5_eq_div_of_shape`.  With no
  normalization scaling (`s = 0`), the four per-digit conservations
  (`N1V5Shift0Conservation`) assemble via `fullDivN1V5_four_step_nat` into the
  Euclidean equation, and `div_quotient_of_normalized` (`s := 0`) +
  `div_of_val256_eq_div` (with the final remainder bound) give the result.
  Bead `evm-asm-wbc4i.9.1`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Quotient
public import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Conservation

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

private theorem val256_lo2 (x y : Word) :
    val256 x y 0 0 = x.toNat + 2 ^ 64 * y.toNat := by
  unfold val256
  simp only [show (0 : Word).toNat = 0 from by decide]
  ring

/-- The v5 n=1 shift=0 quotient word equals `EvmWord.div a b`, from shape. -/
theorem fullDivN1QuotientWordShift0V5_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    fullDivN1QuotientWordShift0V5 a0 a1 a2 a3 b0 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have hb0nz : b0 ≠ 0 := by
    rw [hb1z, hb2z, hb3z] at hbnz; simpa using hbnz
  have rem_eq : ∀ {x0 x1 x2 x3 : Word}, val256 x0 x1 x2 x3 < b0.toNat →
      val256 x0 x1 x2 x3 = x0.toNat := by
    intro x0 x1 x2 x3 h
    obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 b0 h
    rw [h1, h2, h3]; simp [val256]
  have hr3 := rem_eq (s3_rem_lt_shift0 a3 b0 hb0nz hclz)
  have hr2 := rem_eq (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  have hr1 := rem_eq (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  have hr0lt := s0_rem_lt_shift0 a0 a1 a2 a3 b0 hb0nz hclz
  have hr0 := rem_eq hr0lt
  have hacc := fullDivN1V5_four_step_nat
    (a := val256 a0 a1 a2 a3) (b := b0.toNat)
    (q3 := (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1.toNat)
    (q2 := (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1.toNat)
    (q1 := (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1.toNat)
    (q0 := (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1.toNat)
    (u0 := a0.toNat) (u1 := a1.toNat) (u2 := a2.toNat) (u3 := a3.toNat) (u4 := 0)
    (r3 := (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).2.1.toNat)
    (r2 := (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).2.1.toNat)
    (r1 := (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).2.1.toNat)
    (r0 := (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1.toNat)
    (by simp [val256]; ring)
    (by have h := s3_cons_shift0 a3 b0 hb0nz hclz; rw [hr3] at h; simp [val256] at h; omega)
    (by have h := s2_cons_shift0 a2 a3 b0 hb0nz hclz; rw [hr2, val256_lo2] at h; exact h)
    (by have h := s1_cons_shift0 a1 a2 a3 b0 hb0nz hclz; rw [hr1, val256_lo2] at h; exact h)
    (by have h := s0_cons_shift0 a0 a1 a2 a3 b0 hb0nz hclz; rw [hr0, val256_lo2] at h; exact h)
  have hlt : (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1.toNat < b0.toNat := by
    rw [← hr0]; exact hr0lt
  have hq := div_quotient_of_normalized (s := 0) (by simpa using hacc) (by simpa using hlt)
  have hbval : val256 b0 b1 b2 b3 = b0.toNat := by rw [hb1z, hb2z, hb3z]; simp [val256]
  have hqval : val256
      (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).1
      (fullN1S1 b0 0 0 0 a3 0 0 0 0 a2 a1).1
      (fullN1S2 b0 0 0 0 a3 0 0 0 0 a2).1
      (iterN1Call_v5 b0 0 0 0 a3 0 0 0 0).1 =
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
    rw [hbval, ← hq]; simp [val256]; ring
  have hdiv := div_of_val256_eq_div (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) hbnz hqval
  unfold fullDivN1QuotientWordShift0V5
  exact hdiv

end EvmAsm.Evm64
