/-
  EvmAsm.Evm64.DivMod.Spec.N3V5ModRemainder

  **v5 n=3 MOD remainder correctness from shape (shift≠0):**
  `fullModN3RemainderWordV5 = EvmWord.mod a b`.

  The MOD analog of `fullDivN3QuotientWordV5_eq_div_of_shape` (N3V5QuotientShape):
  the final v5 n=3 remainder, denormalized (funnel-shifted down by `fullDivN3Shift b2`),
  equals `EvmWord.mod a b`.  Reuses the same normalized Euclidean telescope as the
  n=3 quotient (`fullDivN3V5_two_step_nat` + the per-digit `_step_of_shape`/
  `_collapse_of_shape` lemmas in N3V5AccQuot), the denormalization identity
  `val256_denormalize`, and the combined bridge `mod_correct_normalized`.  Mirror of
  `fullModN2RemainderWordV5_eq_mod_of_shape` (N2V5ModRemainder), adapted n2→n3
  (2 quotient digits, 3-limb remainder, top limb b2).
-/

import EvmAsm.Evm64.DivMod.Spec.N3V5AccQuot
import EvmAsm.Evm64.EvmWordArith.DenormLemmas

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- **v5 n=3 normalized Euclidean equation from shape (shift≠0).**
    `val256 a · 2^s = Q · (val256 b · 2^s) + R_norm` (mulsub form) together with the
    remainder bound `R_norm < val256 b · 2^s`, where `Q = R1.1·2^64 + R0.1` and
    `R_norm` is the 3-limb normalized remainder.  Same telescope as
    `fullDivN3_acc_quot_eq_div_of_shape`, stopped before the quotient recovery.
    n=3 analog of `fullDivN2_normalized_euclidean_of_shape`. -/
theorem fullDivN3_normalized_euclidean_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
        ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2 ^ 64
          + (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat)
          * (val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat)
        + ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat)) ∧
    ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
        + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat) := by
  have hsnz : fullDivN3Shift b2 ≠ 0 := by unfold fullDivN3Shift; exact hshift_nz
  have hR1 := fullDivN3R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR1c := fullDivN3R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR0valid := n3_next_window_lt (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 _ hR1.2
  have hR0 := fullDivN3R0V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 bltu_0
      hb3z hshift_nz hb2nz hR1c.1 hR0valid hc0 hm0
  have hscaleU := fullDivN3NormU_val256_eq_scaled_with_overflow a0 a1 a2 a3 b2 hsnz
  have hscaleV := fullDivN3NormV_val256_eq_scaled_of_b3_zero b0 b1 b2 b3 hsnz hb3z
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  rw [hvtop] at hscaleV
  have hfirst : val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
      (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * val256 (fullDivN3NormU a0 a1 a2 a3 b2).2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 := by
    rw [← hscaleU]; simp only [EvmWord.val256]; ring
  have hw0 : val256 (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      = (fullDivN3NormU a0 a1 a2 a3 b2).1.toNat
        + 2 ^ 64 * ((fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) := by
    simp only [EvmWord.val256]; ring
  rw [hw0] at hR0
  have htele := fullDivN3V5_two_step_nat hfirst hR1.1 hR0.1
  rw [hscaleV] at htele
  have hlt : (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
      + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
      + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat
      < val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat := by
    rw [← hscaleV]; exact hR0.2
  exact ⟨htele, hlt⟩

/-- The n=3 remainder's top (4th) limb is zero — the 3-limb divisor gives a
    ≤3-limb remainder. -/
theorem fullDivN3R0V5_top_limb_zero_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hvtop := fullDivN3NormV_top_zero_of_shape_shift_nz b0 b1 b2 b3 hb3z hshift_nz
  have hmsb := fullDivN3NormV_msb_of_b2_ne_zero b0 b1 b2 b3 hb2nz
  have hR1 := fullDivN3R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR1c := fullDivN3R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_1 hb3z hshift_nz hb2nz hc1 hm1
  have hR0valid := n3_next_window_lt (fullDivN3NormU a0 a1 a2 a3 b2).1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 _ hR1.2
  have hrw : fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      iterN3V5 bltu_0 (fullDivN3NormV b0 b1 b2 b3).1 (fullDivN3NormV b0 b1 b2 b3).2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 0
        (fullDivN3NormU a0 a1 a2 a3 b2).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 0 := by
    unfold fullDivN3R0V5; dsimp only; rw [hvtop, hR1c.1]
  rw [hrw]
  exact (iterN3V5_collapse bltu_0 _ _ _ _ _ _ _ hmsb hR0valid hc0 hm0).1

/-- Pack the four denormalized v5 n=3 MOD remainder limbs (funnel-shift-down of
    `fullDivN3R0V5`'s remainder by `fullDivN3Shift b2`) into a single `EvmWord`. -/
@[irreducible]
def fullModN3RemainderWordV5 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 1 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 2 =>
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))
    | 3 =>
        (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN3Shift b2).toNat % 64))

/-- **v5 n=3 MOD remainder correctness (shift≠0), from shape + `bltu` matches.**
    `fullModN3RemainderWordV5 = EvmWord.mod a b`. -/
theorem fullModN3RemainderWordV5_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hb3z : b3 = 0) (hshift_nz : (clzResult b2).1 ≠ 0) (hb2nz : b2 ≠ 0)
    (hc1 : bltu_1 = true →
      BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm1 : bltu_1 = false →
      ¬ BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2 (fullDivN3NormV b0 b1 b2 b3).2.2.1)
    (hc0 : bltu_0 = true →
      BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1 = true)
    (hm0 : bltu_0 = false →
      ¬ BitVec.ult (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1) :
    fullModN3RemainderWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0 : Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    exact hb2nz (BitVec.or_eq_zero_iff.mp h2).2
  have heucl := fullDivN3_normalized_euclidean_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  have htop := fullDivN3R0V5_top_limb_zero_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_1 bltu_0 hb3z hshift_nz hb2nz hc1 hm1 hc0 hm0
  -- shift/antiShift normalizations
  have h_shift_pos : 1 ≤ (clzResult b2).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b2).1.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hshift_nz
    · exact h
  have hle63 := clzResult_fst_toNat_le b2
  have hsmod : (fullDivN3Shift b2).toNat % 64 = (fullDivN3Shift b2).toNat := by
    unfold fullDivN3Shift; exact Nat.mod_eq_of_lt (by omega)
  have hamod : (signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64
      = 64 - (fullDivN3Shift b2).toNat := by
    unfold fullDivN3Shift; exact antiShift_toNat_mod_eq h_shift_pos hle63
  have hslt : (fullDivN3Shift b2).toNat < 64 := by unfold fullDivN3Shift; omega
  have hspos : 0 < (fullDivN3Shift b2).toNat := by unfold fullDivN3Shift; omega
  have hr_denorm :
      val256
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN3Shift b2).toNat % 64)))
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64))
      = ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
          + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat)
        / 2 ^ (fullDivN3Shift b2).toNat := by
    rw [hsmod, hamod, val256_denormalize hspos hslt, htop]
    simp only [EvmWord.val256, h0]; ring_nf
  have hmulsub : val256 a0 a1 a2 a3 * 2 ^ (fullDivN3Shift b2).toNat =
      val256 (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 0 0
        * (val256 b0 b1 b2 b3 * 2 ^ (fullDivN3Shift b2).toNat)
      + ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2 ^ 64 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat
        + 2 ^ 128 * (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1.toNat) := by
    rw [show val256 (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 0 0
        = (fullDivN3R1V5 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2 ^ 64
          + (fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
        from by simp only [EvmWord.val256, h0]; ring]
    exact heucl.1
  unfold fullModN3RemainderWordV5
  exact mod_correct_normalized hbnz (fullDivN3Shift b2).toNat hmulsub heucl.2 hr_denorm

/-- Per-limb projection of the n=3 MOD remainder word equality into the four
    `(EvmWord.mod a b).getLimbN` funnel-shift equalities. -/
theorem fullModN3V5_hmods_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_1 bltu_0 : Bool)
    (hmod : fullModN3RemainderWordV5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) |||
          ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN3Shift b2).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN3R0V5 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN3Shift b2).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]; delta fullModN3RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
