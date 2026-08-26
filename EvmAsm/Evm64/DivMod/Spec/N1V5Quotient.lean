/-
  EvmAsm.Evm64.DivMod.Spec.N1V5Quotient

  v5 n=1 quotient word and the carry-zero 4-digit accumulation, en route to
  `fullDivN1QuotientWordV5 = EvmWord.div a b`.

  The per-digit toolkit (`N1V5DigitSteps.lean`) provides, from shape and with NO
  `Carry2NzAll`:
  - the 4 conservations `fullDivN1R{3,2,1,0}V5_conservation_of_shape`
    (`val256(window) = q_k·v0 + val256(remainder)`), and
  - the 4 remainder-lts `fullDivN1R{3,2,1,0}V5_remainder_lt_of_shape`.

  `fullDivN1V5_four_step_nat` below accumulates the four conservation equations
  into `val256(a)·2^s = quotient·(val256(b)·2^s) + r0` (the carries are already
  zero in the v5 per-step conservations, unlike v4's raw form). With the final
  remainder-lt + the scaled-divisor identity `normV.1 = val256(b)·2^s`, this
  feeds `EvmWord.div_correct_normalized` to give
  `fullDivN1QuotientWordV5 = EvmWord.div a b` (next step).

  Bead evm-asm-wbc4i.9.1.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1V5DigitSteps

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The carry-zero 4-digit accumulation — public re-proof of the private
    `fullDivN1_four_step_conservation_nat`, specialized to all carries zero
    (which is exactly what the v5 per-step conservations directly provide). -/
theorem fullDivN1V5_four_step_nat
    {a b q3 q2 q1 q0 u0 u1 u2 u3 u4 r3 r2 r1 r0 : Nat}
    (hfirst : a = u0 + 2 ^ 64 * (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * (u3 + 2 ^ 64 * u4))))
    (hiter3 : u3 + 2 ^ 64 * u4 = q3 * b + r3)
    (hiter2 : u2 + 2 ^ 64 * r3 = q2 * b + r2)
    (hiter1 : u1 + 2 ^ 64 * r2 = q1 * b + r1)
    (hiter0 : u0 + 2 ^ 64 * r1 = q0 * b + r0) :
    a = (q3 * 2 ^ 192 + q2 * 2 ^ 128 + q1 * 2 ^ 64 + q0) * b + r0 := by
  nlinarith

/-- v5 n=1 quotient word: the four digit quotients `fullDivN1R{0,1,2,3}V5.1`
    assembled into a 256-bit word (mirror of `fullDivN1QuotientWord`). -/
def fullDivN1QuotientWordV5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1)

open EvmWord in
/-- A per-step remainder bounded by the divisor occupies only its low limb,
    so its `val256` collapses to `limb0.toNat`. -/
private theorem rem_val_eq_limb0 {x0 x1 x2 x3 v0 : Word}
    (hrem : val256 x0 x1 x2 x3 < v0.toNat) : val256 x0 x1 x2 x3 = x0.toNat := by
  obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word x0 x1 x2 x3 v0 hrem
  rw [h1, h2, h3]; simp [val256]

open EvmWord in
/-- The n=1 normalized single-limb divisor value is `val256(b)·2^shift`. -/
private theorem normV1_eq_scaled_of_shape
    (b0 b1 b2 b3 : Word) (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    (fullDivN1NormV b0 b1 b2 b3).1.toNat =
      val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat := by
  have h := fullDivN1NormV_val256_eq_scaled_of_shape b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  rw [← h, fullDivN1NormV_limb1_eq_zero_of_shape_shift_nz b0 b1 b2 b3 hb1z hshift_nz,
      fullDivN1NormV_limb2_eq_zero_of_shape b0 b1 b2 b3 hb1z hb2z,
      fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  simp [val256]

open EvmWord in
/-- **v5 n=1 quotient correctness, from shape.** The four-digit v5 n=1
    schoolbook computes the exact quotient `EvmWord.div a b` — discharged from
    the divisor shape alone, with NO `Carry2NzAll` and NO
    `Div128AllPhasesNoWrapInv`. Assembles the four per-digit conservations (via
    `fullDivN1V5_four_step_nat`, carries zero) into the normalized Euclidean
    equation, then applies `div_quotient_of_normalized` + `div_of_val256_eq_div`
    with the final remainder bound (`fullDivN1R0V5_remainder_lt_of_shape`) and
    the scaled-limb identities. Bead `evm-asm-wbc4i.9.1`. -/
theorem fullDivN1QuotientWordV5_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  set s := (fullDivN1Shift b0).toNat with hs
  have hu := fullDivN1NormU_val256_eq_scaled a0 a1 a2 a3 b0 hshift_nz
  have hc3 := fullDivN1R3V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc2 := fullDivN1R2V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc1 := fullDivN1R1V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc0 := fullDivN1R0V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hr3 := rem_val_eq_limb0 (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr2 := rem_val_eq_limb0 (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr1 := rem_val_eq_limb0 (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr0lt := fullDivN1R0V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hr0 := rem_val_eq_limb0 hr0lt
  have hvb : (fullDivN1NormV b0 b1 b2 b3).1.toNat = val256 b0 b1 b2 b3 * 2 ^ s := by
    rw [hs]; exact normV1_eq_scaled_of_shape b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  have hacc := fullDivN1V5_four_step_nat
    (a := val256 a0 a1 a2 a3 * 2 ^ s) (b := (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (q3 := (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q2 := (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q1 := (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q0 := (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (u0 := (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat)
    (u1 := (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat)
    (u2 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat)
    (u3 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat)
    (u4 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat)
    (r3 := (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r2 := (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r1 := (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r0 := (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (by rw [← hu]; simp [val256]; ring)
    (by have h := hc3; rw [hr3] at h; simp [val256] at h; omega)
    (by have h := hc2; rw [hr2] at h; simp [val256] at h; omega)
    (by have h := hc1; rw [hr1] at h; simp [val256] at h; omega)
    (by have h := hc0; rw [hr0] at h; simp [val256] at h; omega)
  rw [hvb] at hacc
  have hlt : (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat <
      val256 b0 b1 b2 b3 * 2 ^ s := by rw [← hr0, ← hvb]; exact hr0lt
  have hq := div_quotient_of_normalized (s := s) hacc hlt
  have hqval : val256
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 =
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by rw [← hq]; simp [val256]; ring
  have hdiv := div_of_val256_eq_div (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3) hbnz hqval
  unfold fullDivN1QuotientWordV5
  exact hdiv

/-- **v5 dispatch-post bridge.** Decompose the v5 n=1 quotient-word equality
    `fullDivN1QuotientWordV5 = EvmWord.div a b` into the four per-limb
    `getLimbN`/digit equalities that the n=1 lane wrapper feeds to
    `divStackDispatchPost`.  Pure `fromLimbs` projection — the v5 analog of
    `fullDivN1_hdivs_of_word_eq`.  Bead `evm-asm-wbc4i.9.1.4`. -/
theorem fullDivN1V5_hdivs_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN1QuotientWordV5 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]; delta fullDivN1QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]; delta fullDivN1QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]; delta fullDivN1QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]; delta fullDivN1QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

open EvmWord in
/-- **v5 n=1 remainder correctness, from shape.** The final normalized remainder
    `(fullDivN1R0V5 …).2.1`, shifted down by the normalization shift `s`,
    equals `EvmWord.mod a b`.  Same Euclidean accumulation as the quotient, then
    `mod_remainder_of_normalized` (`r_norm / 2^s = a % b`) + `mod_of_val256_eq_mod`.
    The MOD analog of `fullDivN1QuotientWordV5_eq_div_of_shape`.  Bead
    `evm-asm-wbc4i.9.1`. -/
theorem fullDivN1V5_remainder_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.fromLimbs (fun i : Fin 4 => match i with
      | 0 => (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
               (fullDivN1Shift b0).toNat
      | 1 => 0 | 2 => 0 | 3 => 0)
    = EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  set s := (fullDivN1Shift b0).toNat with hs
  have hu := fullDivN1NormU_val256_eq_scaled a0 a1 a2 a3 b0 hshift_nz
  have hc3 := fullDivN1R3V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc2 := fullDivN1R2V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc1 := fullDivN1R1V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hc0 := fullDivN1R0V5_conservation_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hr3 := rem_val_eq_limb0 (fullDivN1R3V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr2 := rem_val_eq_limb0 (fullDivN1R2V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr1 := rem_val_eq_limb0 (fullDivN1R1V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz)
  have hr0lt := fullDivN1R0V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hshift_nz
  have hr0 := rem_val_eq_limb0 hr0lt
  have hvb : (fullDivN1NormV b0 b1 b2 b3).1.toNat = val256 b0 b1 b2 b3 * 2 ^ s := by
    rw [hs]; exact normV1_eq_scaled_of_shape b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz
  have hacc := fullDivN1V5_four_step_nat
    (a := val256 a0 a1 a2 a3 * 2 ^ s) (b := (fullDivN1NormV b0 b1 b2 b3).1.toNat)
    (q3 := (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q2 := (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q1 := (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (q0 := (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
    (u0 := (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat)
    (u1 := (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat)
    (u2 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat)
    (u3 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat)
    (u4 := (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat)
    (r3 := (fullDivN1R3V5 true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r2 := (fullDivN1R2V5 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r1 := (fullDivN1R1V5 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (r0 := (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat)
    (by rw [← hu]; simp [val256]; ring)
    (by have h := hc3; rw [hr3] at h; simp [val256] at h; omega)
    (by have h := hc2; rw [hr2] at h; simp [val256] at h; omega)
    (by have h := hc1; rw [hr1] at h; simp [val256] at h; omega)
    (by have h := hc0; rw [hr0] at h; simp [val256] at h; omega)
  rw [hvb] at hacc
  have hlt : (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat <
      val256 b0 b1 b2 b3 * 2 ^ s := by rw [← hr0, ← hvb]; exact hr0lt
  have hmod := mod_remainder_of_normalized (s := s) hacc hlt
  have hrval : val256
      ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> s) 0 0 0 =
      val256 a0 a1 a2 a3 % val256 b0 b1 b2 b3 := by
    simp only [val256, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simpa [val256] using hmod
  exact mod_of_val256_eq_mod hbnz hrval

end EvmAsm.Evm64
