/-
  EvmAsm.Evm64.DivMod.Spec.N2V5ModRemainder

  **v5 n=2 MOD remainder correctness from shape (shift≠0):**
  `fullModN2RemainderWordV5 = EvmWord.mod a b`.

  The MOD analog of `fullDivN2QuotientWordV5_eq_div_of_shape` (N2V5QuotientShape):
  the final v5 n=2 remainder, denormalized (funnel-shifted down by `fullDivN2Shift`),
  equals `EvmWord.mod a b`.  Uses the same normalized Euclidean core
  `fullDivN2_normalized_euclidean_of_shape` (N2V5NormScaled), the chained R0
  collapse, the denormalization identity `val256_denormalize`, and the combined
  bridge `mod_correct_normalized`.  Bead `evm-asm-wbc4i.9.2`.
-/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.EvmWordArith.DenormLemmas

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- The chained R0 collapse (R0's remainder high two limbs are zero), derived
    from shape + the `bltu` path matches by threading R2→R1→R0. -/
theorem fullDivN2R0V5_collapse_chained_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 = 0 ∧
    (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 = 0 := by
  have hfwv := fullDivN2_first_window_valid a0 a1 a2 a3 b0 b1 b2 b3 hb2z hb3z hshift_nz hb1nz
  have hR2 := fullDivN2R2V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR2c := fullDivN2R2V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 hb2z hb3z hshift_nz hb1nz hfwv hc2 hm2
  have hR1valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR2.2
  have hR1 := fullDivN2R1V5_step_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR1c := fullDivN2R1V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 hb2z hb3z hshift_nz hb1nz hR2c.1 hR2c.2 hR1valid hc1 hm1
  have hR0valid := n2_next_window_lt (fullDivN2NormU a0 a1 a2 a3 b1).1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1 (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 _ hR1.2
  exact fullDivN2R0V5_collapse_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hR1c.1 hR1c.2 hR0valid hc0 hm0

/-- Pack the four denormalized v5 n=2 MOD remainder limbs (funnel-shift-down of
    `fullDivN2R0V5`'s remainder by `fullDivN2Shift b1`) into a single `EvmWord`. -/
@[irreducible]
def fullModN2RemainderWordV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))
    | 1 =>
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))
    | 2 =>
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))
    | 3 =>
        (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN2Shift b1).toNat % 64))

/-- **v5 n=2 MOD remainder correctness (shift≠0), from shape + `bltu` matches.**
    `fullModN2RemainderWordV5 = EvmWord.mod a b`. -/
theorem fullModN2RemainderWordV5_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    exact hb1nz (BitVec.or_eq_zero_iff.mp h3).2
  have heucl := fullDivN2_normalized_euclidean_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  have hcol := fullDivN2R0V5_collapse_chained_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  -- shift/antiShift normalizations
  have h_shift_pos : 1 ≤ (clzResult b1).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b1).1.toNat with h | h
    · exfalso; apply hshift_nz; exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hle63 := clzResult_fst_toNat_le b1
  have hsmod : (fullDivN2Shift b1).toNat % 64 = (fullDivN2Shift b1).toNat := by
    unfold fullDivN2Shift; exact Nat.mod_eq_of_lt (by omega)
  have hamod : (signExtend12 (0:BitVec 12) - fullDivN2Shift b1).toNat % 64 = 64 - (fullDivN2Shift b1).toNat := by
    unfold fullDivN2Shift; exact antiShift_toNat_mod_eq h_shift_pos hle63
  have hslt : (fullDivN2Shift b1).toNat < 64 := by unfold fullDivN2Shift; omega
  have hspos : 0 < (fullDivN2Shift b1).toNat := by unfold fullDivN2Shift; omega
  -- denormalization identity
  have hr_denorm :
      val256
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0:BitVec 12) - fullDivN2Shift b1).toNat % 64)))
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64))
      = ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
          + 2^64 * (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat)
        / 2^(fullDivN2Shift b1).toNat := by
    rw [hsmod, hamod, val256_denormalize hspos hslt, hcol.1, hcol.2]
    simp only [EvmWord.val256, h0]; ring_nf
  -- assemble via mod_correct_normalized; convert Q-sum to val256 form
  have hmulsub : val256 a0 a1 a2 a3 * 2^(fullDivN2Shift b1).toNat =
      val256 (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 0
        * (val256 b0 b1 b2 b3 * 2^(fullDivN2Shift b1).toNat)
      + ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1.toNat
        + 2^64 * (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1.toNat) := by
    rw [show val256 (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
        (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 0
        = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^128
          + (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat * 2^64
          + (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
        from by simp only [EvmWord.val256, h0]; ring]
    exact heucl.1
  unfold fullModN2RemainderWordV5
  exact mod_correct_normalized hbnz (fullDivN2Shift b1).toNat hmulsub heucl.2 hr_denorm

/-- **MOD getLimbN bridge.** Decompose the remainder-word equality into the four
    per-limb `(mod a b).getLimbN k = denorm-limb_k` facts the n=2 MOD lane wrapper
    feeds to `modStackDispatchPost`.  Pure `fromLimbs` projection — MOD analog of
    `fullDivN2V5_hdivs_of_word_eq`. -/
theorem fullModN2V5_hmods_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hmod : fullModN2RemainderWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) |||
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN2Shift b1).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN2Shift b1).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]; delta fullModN2RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]; delta fullModN2RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]; delta fullModN2RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]; delta fullModN2RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_3

end EvmAsm.Evm64
