/-
  EvmAsm.Evm64.EvmWordArith.DivN3NormVStructure

  Structural facts about the normalised divisor `fullDivN3NormV` under the
  n=3 shape predicate (`b3 = 0`, `b2 ≠ 0`) and `shift_nz`.

  Two facts are proved here:
    1. `fullDivN3NormV_top_zero_of_shape_shift_nz`: the top limb v3_norm is 0.
    2. `fullDivN3NormV_msb_of_shift_nz`: the third limb v2_norm has its MSB
       set, i.e., `2^63 ≤ v2_norm.toNat`.

  These are the two normalisation hypotheses required by the N3 MAX-branch
  closure-form theorems (`isAddbackCarry2NzN3Max_at_canonical_bltu{1,0}_false`
  in `N3MaxBranchFromInvariant`).  Closing them here turns each closure into
  a theorem with shape-only public hypotheses (mod the still-named c3
  reachability invariant).
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
public import EvmAsm.Evm64.EvmWordArith.CLZLemmas
public import EvmAsm.Evm64.EvmWordArith.MaxTrialVacuity

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Auxiliary: when `shift = clzResult b2 .1` is in `[1, 63]`, the antiShift
    word's `toNat % 64` equals `64 - shift`.  Used by the structural facts
    below to bring the shift amount into a usable range. -/
private theorem fullDivN3AntiShift_toNat_mod_64
    (b2 : Word) (hs_nz : (clzResult b2).1 ≠ 0) :
    (fullDivN3AntiShift b2).toNat % 64 = 64 - (clzResult b2).1.toNat := by
  rw [fullDivN3AntiShift_unfold, fullDivN3Shift_unfold]
  -- antiShift = (signExtend12 0 : Word) - clzResult b2 .1
  --           = (0 : Word) - clzResult b2 .1
  --           = - clz  (in BitVec 64 arithmetic)
  -- toNat of negation: (-x).toNat = (2^64 - x.toNat) % 2^64 when x ≠ 0.
  have hclz_le : (clzResult b2).1.toNat ≤ 63 := clzResult_fst_toNat_le b2
  have hclz_pos : 0 < (clzResult b2).1.toNat := by
    by_contra h
    have : (clzResult b2).1.toNat = 0 := by omega
    exact hs_nz (BitVec.eq_of_toNat_eq (by rw [this]; rfl))
  have h_se0 : (signExtend12 (0 : BitVec 12) : Word) = (0 : Word) := by decide
  rw [h_se0]
  -- ((0 : Word) - clz).toNat = 2^64 - clz.toNat (since clz.toNat ∈ [1, 63]).
  have h_sub_toNat : ((0 : Word) - (clzResult b2).1).toNat =
      2^64 - (clzResult b2).1.toNat := by
    rw [BitVec.toNat_sub]
    show (2^64 - (clzResult b2).1.toNat + 0) % 2^64 = 2^64 - (clzResult b2).1.toNat
    have : 2^64 - (clzResult b2).1.toNat < 2^64 := by omega
    rw [Nat.add_zero]
    exact Nat.mod_eq_of_lt this
  rw [h_sub_toNat]
  -- (2^64 - clz) % 64 = (64 - clz) when 0 < clz ≤ 63.
  have h_2_64_eq : (2:Nat)^64 = 64 * 2^58 := by norm_num
  -- 2^64 - clz = 64 * 2^58 - clz; mod 64: same as (-clz) % 64.
  have h_split : 2^64 - (clzResult b2).1.toNat =
      (64 - (clzResult b2).1.toNat) + 64 * (2^58 - 1) := by
    rw [h_2_64_eq]
    have h_pow_pos : 0 < (2:Nat)^58 := by positivity
    have h_64sub : (clzResult b2).1.toNat ≤ 64 := by omega
    -- 64 * 2^58 - clz = (64 - clz) + 64*(2^58 - 1)   when clz ≤ 64.
    have h_expand : (64 - (clzResult b2).1.toNat) + 64 * (2^58 - 1) =
        64 - (clzResult b2).1.toNat + (64 * 2^58 - 64) := by
      have : 64 * (2^58 - 1) = 64 * 2^58 - 64 := by
        rw [Nat.mul_sub_one]
      omega
    omega
  rw [h_split]
  rw [Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

/-- Under n=3 shape (`b3 = 0`) and `shift_nz`, the top limb of the normalised
    `v` is zero. -/
theorem fullDivN3NormV_top_zero_of_shape_shift_nz
    (b0 b1 b2 b3 : Word)
    (hb3z : b3 = 0)
    (hshift_nz : (clzResult b2).1 ≠ 0) :
    (fullDivN3NormV b0 b1 b2 b3).2.2.2 = 0 := by
  rw [fullDivN3NormV_unfold]
  show (b3 <<< ((fullDivN3Shift b2).toNat % 64)) |||
       (b2 >>> ((fullDivN3AntiShift b2).toNat % 64)) = 0
  rw [hb3z]
  -- (0 <<< s) = 0
  have h_zero_shl : (0 : Word) <<< ((fullDivN3Shift b2).toNat % 64) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft]
    simp
  rw [h_zero_shl]
  -- 0 ||| x = x
  have h_or_left_zero : ∀ x : Word, (0 : Word) ||| x = x := fun x => by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or]; simp
  rw [h_or_left_zero]
  -- Now goal: b2 >>> (antiShift.toNat % 64) = 0.
  -- antiShift.toNat % 64 = 64 - shift; and b2.toNat < 2^(64 - shift).
  rw [fullDivN3AntiShift_toNat_mod_64 b2 hshift_nz]
  rw [ushiftRight_eq_zero_iff]
  exact clzResult_fst_top_bound b2

/-- Under `b2 ≠ 0`, the third limb of the normalised `v` has its MSB set,
    i.e., `2^63 ≤ v.2.2.1.toNat`.  Uses `b3_shifted_ge_pow63` from
    `MaxTrialVacuity` (specialised for `b3` but generic over the input). -/
theorem fullDivN3NormV_msb_of_b2_ne_zero
    (b0 b1 b2 b3 : Word)
    (hb2nz : b2 ≠ 0) :
    2^63 ≤ (fullDivN3NormV b0 b1 b2 b3).2.2.1.toNat := by
  rw [fullDivN3NormV_unfold]
  show 2^63 ≤ ((b2 <<< ((fullDivN3Shift b2).toNat % 64)) |||
                (b1 >>> ((fullDivN3AntiShift b2).toNat % 64))).toNat
  rw [fullDivN3Shift_unfold]
  rw [BitVec.toNat_or]
  -- (x ||| y).toNat ≥ x.toNat (bitwise OR can only increase value)
  have h_or_ge : (b2 <<< ((clzResult b2).1.toNat % 64)).toNat ≤
      ((b2 <<< ((clzResult b2).1.toNat % 64)).toNat |||
       (b1 >>> ((fullDivN3AntiShift b2).toNat % 64)).toNat) :=
    Nat.left_le_or
  -- (b2 <<< clz(b2)).toNat ≥ 2^63 by the existing MaxTrialVacuity lemma.
  have h_b2_shifted := b3_shifted_ge_pow63 (b3 := b2) hb2nz
  exact le_trans h_b2_shifted h_or_ge

end EvmAsm.Evm64
