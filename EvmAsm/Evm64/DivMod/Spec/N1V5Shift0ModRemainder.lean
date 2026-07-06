/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Shift0ModRemainder

  v5 n=1 **shift=0** MOD remainder correctness: the shift=0 schoolbook leaves the
  exact remainder `EvmWord.mod a b` in the low u-cell, from the divisor shape
  `(clzResult b0).1 = 0` (single-limb divisor, already top-bit aligned, no
  normalization scaling).

  MOD counterpart of `fullDivN1QuotientWordShift0V5_eq_div_of_shape`
  (N1V5Shift0QuotientCorrect): same `fullDivN1V5_four_step_nat` Euclidean
  accumulation, but `mod_remainder_of_normalized` (`s := 0`, so `r / 2^0 = a % b`)
  + `mod_of_val256_eq_mod` instead of the quotient bridges.  The shift=0 MOD
  epilogue (`evm_mod_shift0_epilogue_spec_v5_noNop`) loads the un-normalized
  remainder u-cells directly, so the assembled remainder word packs
  `(fullN1S0 …).2.{1,2.1,2.2.1,2.2.2.1}` with no funnel-shift.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Quotient
import EvmAsm.Evm64.DivMod.Spec.N1V5Shift0Conservation

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

private theorem val256_lo2_mod (x y : Word) :
    val256 x y 0 0 = x.toNat + 2 ^ 64 * y.toNat := by
  unfold val256
  simp only [show (0 : Word).toNat = 0 from by decide]
  ring

/-- Pack the four shift=0 MOD remainder limbs (the loop's un-normalized u-cells,
    read directly by the shift=0 MOD epilogue) into a single `EvmWord`. -/
@[irreducible]
def fullModN1RemainderWordShift0V5 (a0 a1 a2 a3 b0 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 => match i with
    | 0 => (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1
    | 1 => (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.1
    | 2 => (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.1
    | 3 => (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.2.2.2.1)

/-- **v5 n=1 shift=0 MOD remainder correctness, from shape.**
    `fullModN1RemainderWordShift0V5 = EvmWord.mod a b`. -/
theorem fullModN1RemainderWordShift0V5_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    fullModN1RemainderWordShift0V5 a0 a1 a2 a3 b0 =
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have hb0nz : b0 ≠ 0 := by
    rw [hb1z, hb2z, hb3z] at hbnz; simpa using hbnz
  have rem_eq : ∀ {x0 x1 x2 x3 : Word}, val256 x0 x1 x2 x3 < b0.toNat →
      x1 = 0 ∧ x2 = 0 ∧ x3 = 0 := by
    intro x0 x1 x2 x3 h
    exact val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 b0 h
  have rem_val : ∀ {x0 x1 x2 x3 : Word}, val256 x0 x1 x2 x3 < b0.toNat →
      val256 x0 x1 x2 x3 = x0.toNat := by
    intro x0 x1 x2 x3 h
    obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 b0 h
    rw [h1, h2, h3]; simp [val256]
  have hr3 := rem_val (s3_rem_lt_shift0 a3 b0 hb0nz hclz)
  have hr2 := rem_val (s2_rem_lt_shift0 a2 a3 b0 hb0nz hclz)
  have hr1 := rem_val (s1_rem_lt_shift0 a1 a2 a3 b0 hb0nz hclz)
  have hr0lt := s0_rem_lt_shift0 a0 a1 a2 a3 b0 hb0nz hclz
  have hr0 := rem_val hr0lt
  -- high remainder limbs collapse to zero (remainder < b0 < 2^64)
  obtain ⟨hc1, hc2, hc3⟩ := rem_eq hr0lt
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
    (by have h := s2_cons_shift0 a2 a3 b0 hb0nz hclz; rw [hr2, val256_lo2_mod] at h; exact h)
    (by have h := s1_cons_shift0 a1 a2 a3 b0 hb0nz hclz; rw [hr1, val256_lo2_mod] at h; exact h)
    (by have h := s0_cons_shift0 a0 a1 a2 a3 b0 hb0nz hclz; rw [hr0, val256_lo2_mod] at h; exact h)
  have hlt : (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1.toNat < b0.toNat := by
    rw [← hr0]; exact hr0lt
  have hmod := mod_remainder_of_normalized (s := 0) (by simpa using hacc) (by simpa using hlt)
  have hbval : val256 b0 b1 b2 b3 = b0.toNat := by rw [hb1z, hb2z, hb3z]; simp [val256]
  have hrval : val256 (fullN1S0 b0 0 0 0 a3 0 0 0 0 a2 a1 a0).2.1 0 0 0 =
      val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
    rw [hbval]
    simp only [val256, show (0 : Word).toNat = 0 from by decide]
    simpa using hmod
  -- collapse the high limbs of the assembled word, then close via the single-limb value
  unfold fullModN1RemainderWordShift0V5
  rw [hc1, hc2, hc3]
  exact mod_of_val256_eq_mod hbnz hrval

/-- Lane (`a b : EvmWord`) form of the shift=0 MOD remainder word correctness. -/
theorem fullModN1RemainderWordShift0V5_eq_mod_lane_of_shape
    {a b : EvmWord} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hclz : (clzResult b0).1 = 0) :
    fullModN1RemainderWordShift0V5 a0 a1 a2 a3 b0 = EvmWord.mod a b := by
  have hraw := fullModN1RemainderWordShift0V5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hclz
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

end EvmAsm.Evm64
