/-
  EvmAsm.Evm64.EvmWordArith.DivN2NormVStructure

  Structural facts about the normalised divisor `fullDivN2NormV` under the
  n=2 shape predicate (`b3 = 0`, `b2 = 0`, `b1 ≠ 0`) and `shift_nz`.

  Three facts are proved here:
    1. `fullDivN2NormV_top_zero_of_shape_shift_nz`: `v3_norm = 0`.
    2. `fullDivN2NormV_v2_zero_of_shape_shift_nz`: `v2_norm = 0`.
    3. `fullDivN2NormV_msb_of_b1_ne_zero`: `2^63 ≤ v1_norm.toNat`.

  These are the three normalisation hypotheses required by the N2 MAX-branch
  closure-form theorems (`isAddbackCarry2NzN2Max_at_canonical_bltu{2,1,0}_false`
  in `N2MaxBranchFromInvariant`).  Mirrors `DivN3NormVStructure` for the
  n=2 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN2Bundle.Base
public import EvmAsm.Evm64.EvmWordArith.CLZLemmas
public import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Auxiliary: when `shift = clzResult b1 .1` is in `[1, 63]`, the antiShift
    word's `toNat % 64` equals `64 - shift`.  Used by the structural facts
    below to bring the shift amount into a usable range. -/
private theorem fullDivN2AntiShift_toNat_mod_64
    (b1 : Word) (hs_nz : (clzResult b1).1 ≠ 0) :
    (fullDivN2AntiShift b1).toNat % 64 = 64 - (clzResult b1).1.toNat := by
  rw [fullDivN2AntiShift_unfold, fullDivN2Shift_unfold]
  have hclz_le : (clzResult b1).1.toNat ≤ 63 := clzResult_fst_toNat_le b1
  have hclz_pos : 0 < (clzResult b1).1.toNat := by
    by_contra h
    have : (clzResult b1).1.toNat = 0 := by omega
    exact hs_nz (BitVec.eq_of_toNat_eq (by rw [this]; rfl))
  have h_se0 : (signExtend12 (0 : BitVec 12) : Word) = (0 : Word) := by decide
  rw [h_se0]
  have h_sub_toNat : ((0 : Word) - (clzResult b1).1).toNat =
      2^64 - (clzResult b1).1.toNat := by
    rw [BitVec.toNat_sub]
    show (2^64 - (clzResult b1).1.toNat + 0) % 2^64 = 2^64 - (clzResult b1).1.toNat
    have : 2^64 - (clzResult b1).1.toNat < 2^64 := by omega
    rw [Nat.add_zero]
    exact Nat.mod_eq_of_lt this
  rw [h_sub_toNat]
  have h_split : 2^64 - (clzResult b1).1.toNat =
      (64 - (clzResult b1).1.toNat) + 64 * (2^58 - 1) := by
    have h_2_64_eq : (2:Nat)^64 = 64 * 2^58 := by norm_num
    rw [h_2_64_eq]
    have h_expand : (64 - (clzResult b1).1.toNat) + 64 * (2^58 - 1) =
        64 - (clzResult b1).1.toNat + (64 * 2^58 - 64) := by
      have : 64 * (2^58 - 1) = 64 * 2^58 - 64 := by rw [Nat.mul_sub_one]
      omega
    omega
  rw [h_split]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Under n=2 shape (`b3 = 0`, `b2 = 0`), the top limb of the normalised `v`
    is zero.  Note: independent of `shift_nz` — both shifted-in inputs are
    zero, so the OR is zero unconditionally. -/
theorem fullDivN2NormV_top_zero_of_shape
    (b0 b1 b2 b3 : Word)
    (hb3z : b3 = 0)
    (hb2z : b2 = 0) :
    (fullDivN2NormV b0 b1 b2 b3).2.2.2 = 0 := by
  rw [fullDivN2NormV_unfold]
  show (b3 <<< ((fullDivN2Shift b1).toNat % 64)) |||
       (b2 >>> ((fullDivN2AntiShift b1).toNat % 64)) = 0
  rw [hb3z, hb2z]
  have h_zero_shl : (0 : Word) <<< ((fullDivN2Shift b1).toNat % 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft]; simp
  have h_zero_shr : (0 : Word) >>> ((fullDivN2AntiShift b1).toNat % 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight]; simp
  rw [h_zero_shl, h_zero_shr]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]; simp

/-- Under n=2 shape (`b2 = 0`) and `shift_nz`, the third limb of the
    normalised `v` is zero.  Symmetric to the top-limb case in
    `DivN3NormVStructure`, with `b1` in the role of the n=3 `b2`. -/
theorem fullDivN2NormV_v2_zero_of_shape_shift_nz
    (b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0)
    (hshift_nz : (clzResult b1).1 ≠ 0) :
    (fullDivN2NormV b0 b1 b2 b3).2.2.1 = 0 := by
  rw [fullDivN2NormV_unfold]
  show (b2 <<< ((fullDivN2Shift b1).toNat % 64)) |||
       (b1 >>> ((fullDivN2AntiShift b1).toNat % 64)) = 0
  rw [hb2z]
  have h_zero_shl : (0 : Word) <<< ((fullDivN2Shift b1).toNat % 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft]; simp
  rw [h_zero_shl]
  have h_or_left_zero : ∀ x : Word, (0 : Word) ||| x = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or]; simp
  rw [h_or_left_zero]
  rw [fullDivN2AntiShift_toNat_mod_64 b1 hshift_nz]
  rw [ushiftRight_eq_zero_iff]
  exact clzResult_fst_top_bound b1

/-- Under `b1 ≠ 0`, the second limb of the normalised `v` has its MSB set,
    i.e., `2^63 ≤ v.2.1.toNat`. -/
theorem fullDivN2NormV_msb_of_b1_ne_zero
    (b0 b1 b2 b3 : Word)
    (hb1nz : b1 ≠ 0) :
    2^63 ≤ (fullDivN2NormV b0 b1 b2 b3).2.1.toNat := by
  rw [fullDivN2NormV_unfold]
  show 2^63 ≤ ((b1 <<< ((fullDivN2Shift b1).toNat % 64)) |||
                (b0 >>> ((fullDivN2AntiShift b1).toNat % 64))).toNat
  rw [fullDivN2Shift_unfold]
  rw [BitVec.toNat_or]
  have h_or_ge : (b1 <<< ((clzResult b1).1.toNat % 64)).toNat ≤
      ((b1 <<< ((clzResult b1).1.toNat % 64)).toNat |||
       (b0 >>> ((fullDivN2AntiShift b1).toNat % 64)).toNat) :=
    Nat.left_le_or
  have h_b1_shifted := b3_shifted_ge_pow63 (b3 := b1) hb1nz
  exact le_trans h_b1_shifted h_or_ge

end EvmAsm.Evm64
