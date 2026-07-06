/-
  EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge

  Explicit-limb n=1 quotient bridge for Unified stack wrapper call sites.
-/

import EvmAsm.Evm64.DivMod.Spec.N1QuotientWord
import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The low normalized n=1 divisor limb is the shifted original low limb. -/
theorem fullDivN1NormV_limb0_eq
    (b0 b1 b2 b3 : Word) :
    (fullDivN1NormV b0 b1 b2 b3).1 =
      b0 <<< ((fullDivN1Shift b0).toNat % 64) := by
  unfold fullDivN1NormV
  simp

/-- A nonzero n=1 divisor has a nonzero low normalized divisor limb. -/
theorem fullDivN1NormV_limb0_ne_zero_of_b0_ne_zero
    (b0 b1 b2 b3 : Word) (hb0nz : b0 ≠ 0) :
    (fullDivN1NormV b0 b1 b2 b3).1 ≠ 0 := by
  intro h_zero
  have h_ge : (b0 <<< ((clzResult b0).1.toNat % 64)).toNat ≥ 2^63 :=
    b3_shifted_ge_pow63 hb0nz
  have h_limb0 := fullDivN1NormV_limb0_eq b0 b1 b2 b3
  unfold fullDivN1Shift at h_limb0
  have h_nat : (b0 <<< ((clzResult b0).1.toNat % 64)).toNat = 0 := by
    rw [← h_limb0, h_zero]
    rfl
  omega

/-- Nonzero shape needed by the `v3 = 0` n=1 conservation lemma. -/
theorem fullDivN1NormV_low3_or_zero_ne_zero_of_b0_ne_zero
    (b0 b1 b2 b3 : Word) (hb0nz : b0 ≠ 0) :
    (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
  intro h_zero
  have h_limb0_ne :=
    fullDivN1NormV_limb0_ne_zero_of_b0_ne_zero b0 b1 b2 b3 hb0nz
  apply h_limb0_ne
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun w => w.getLsbD i) h_zero
  simp only [BitVec.getLsbD_or] at hh
  revert hh
  cases (fullDivN1NormV b0 b1 b2 b3).1.getLsbD i <;>
    cases (fullDivN1NormV b0 b1 b2 b3).2.1.getLsbD i <;>
    cases (fullDivN1NormV b0 b1 b2 b3).2.2.1.getLsbD i <;> simp

/-- The n=1 runtime divisor-shape hypotheses imply the low divisor limb is nonzero. -/
theorem fullDivN1_b0_ne_zero_of_shape
    (b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    b0 ≠ 0 := by
  subst b1
  subst b2
  subst b3
  simpa using hbnz

/-- Runtime n=1 divisor-shape form of the nonzero hypothesis needed by the
    `v3 = 0` conservation lemma. -/
theorem fullDivN1NormV_low3_or_zero_ne_zero_of_shape
    (b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    (fullDivN1NormV b0 b1 b2 b3).1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.1 |||
        (fullDivN1NormV b0 b1 b2 b3).2.2.1 ||| (0 : Word) ≠ 0 := by
  exact fullDivN1NormV_low3_or_zero_ne_zero_of_b0_ne_zero b0 b1 b2 b3
    (fullDivN1_b0_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)

/-- Under the n=1 divisor shape, normalized limb 1 is the low limb's
    anti-shift spill. -/
theorem fullDivN1NormV_limb1_eq_of_shape
    (b0 b1 b2 b3 : Word) (hb1z : b1 = 0) :
    (fullDivN1NormV b0 b1 b2 b3).2.1 =
      b0 >>> ((fullDivN1AntiShift b0).toNat % 64) := by
  subst b1
  unfold fullDivN1NormV
  simp

/-- Under the n=1 divisor shape, the second high normalized divisor limb is zero. -/
theorem fullDivN1NormV_limb2_eq_zero_of_shape
    (b0 b1 b2 b3 : Word) (hb1z : b1 = 0) (hb2z : b2 = 0) :
    (fullDivN1NormV b0 b1 b2 b3).2.2.1 = 0 := by
  subst b1
  subst b2
  unfold fullDivN1NormV
  simp

/-- Under the n=1 divisor shape, the high normalized divisor limb is zero. -/
theorem fullDivN1NormV_limb3_eq_zero_of_shape
    (b0 b1 b2 b3 : Word) (hb2z : b2 = 0) (hb3z : b3 = 0) :
    (fullDivN1NormV b0 b1 b2 b3).2.2.2 = 0 := by
  subst b2
  subst b3
  unfold fullDivN1NormV
  simp

/-- Rewrite a normalized n=1 `Carry2NzAll` hypothesis to the zero-top form
    consumed by `iterN1_val256_conservation_v3_zero_of_carry2`. -/
theorem fullDivN1NormV_carry2_zeroTop_of_shape
    (b0 b1 b2 b3 : Word)
    (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      0 := by
  rw [← fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact hcarry2

/-- One n=1 iteration preserves the val256 Euclidean identity under the runtime
    n=1 divisor-shape hypotheses. -/
theorem iterN1_fullDivN1NormV_val256_conservation_of_shape
    (bltu : Bool) (b0 b1 b2 b3 u0 u1 u2 u3 uTop : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let out := iterN1 bltu v.1 v.2.1 v.2.2.1 v.2.2.2 u0 u1 u2 u3 uTop
    EvmWord.val256 u0 u1 u2 u3 + uTop.toNat * 2^256 =
      out.1.toNat * EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 +
        EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
        out.2.2.2.2.2.toNat * 2^256 := by
  dsimp only
  rw [fullDivN1NormV_limb3_eq_zero_of_shape b0 b1 b2 b3 hb2z hb3z]
  exact iterN1_val256_conservation_v3_zero_of_carry2 bltu
    (fullDivN1NormV b0 b1 b2 b3).1
    (fullDivN1NormV b0 b1 b2 b3).2.1
    (fullDivN1NormV b0 b1 b2 b3).2.2.1
    u0 u1 u2 u3 uTop
    (fullDivN1NormV_low3_or_zero_ne_zero_of_shape b0 b1 b2 b3 hbnz hb1z hb2z hb3z)
    (fullDivN1NormV_carry2_zeroTop_of_shape b0 b1 b2 b3 hb2z hb3z hcarry2)

/-- Val256 conservation specialized to the first n=1 schoolbook iteration. -/
theorem fullDivN1R3_val256_conservation_of_shape
    (bltu_3 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    EvmWord.val256 u.2.2.2.1 u.2.2.2.2 0 0 =
      r3.1.toNat * EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 +
        EvmWord.val256 r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1 +
        r3.2.2.2.2.2.toNat * 2^256 := by
  dsimp only
  unfold fullDivN1R3
  dsimp only
  have h := iterN1_fullDivN1NormV_val256_conservation_of_shape bltu_3
    b0 b1 b2 b3
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
    0 0 0 hbnz hb1z hb2z hb3z hcarry2
  dsimp only at h
  simpa using h

/-- Val256 conservation specialized to the second n=1 schoolbook iteration. -/
theorem fullDivN1R2_val256_conservation_of_shape
    (bltu_3 bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r3 := fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    EvmWord.val256 u.2.2.1 r3.2.1 r3.2.2.1 r3.2.2.2.1 +
        r3.2.2.2.2.1.toNat * 2^256 =
      r2.1.toNat * EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 +
        EvmWord.val256 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 +
        r2.2.2.2.2.2.toNat * 2^256 := by
  dsimp only
  unfold fullDivN1R2
  dsimp only
  have h := iterN1_fullDivN1NormV_val256_conservation_of_shape bltu_2
    b0 b1 b2 b3
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hbnz hb1z hb2z hb3z hcarry2
  dsimp only at h
  simpa using h

/-- Val256 conservation specialized to the third n=1 schoolbook iteration. -/
theorem fullDivN1R1_val256_conservation_of_shape
    (bltu_3 bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r2 := fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    EvmWord.val256 u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 +
        r2.2.2.2.2.1.toNat * 2^256 =
      r1.1.toNat * EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 +
        EvmWord.val256 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 +
        r1.2.2.2.2.2.toNat * 2^256 := by
  dsimp only
  unfold fullDivN1R1
  dsimp only
  have h := iterN1_fullDivN1NormV_val256_conservation_of_shape bltu_1
    b0 b1 b2 b3
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hbnz hb1z hb2z hb3z hcarry2
  dsimp only at h
  simpa using h

/-- Val256 conservation specialized to the final n=1 schoolbook iteration. -/
theorem fullDivN1R0_val256_conservation_of_shape
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2) :
    let v := fullDivN1NormV b0 b1 b2 b3
    let u := fullDivN1NormU a0 a1 a2 a3 b0
    let r1 := fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    let r0 := fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    EvmWord.val256 u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 +
        r1.2.2.2.2.1.toNat * 2^256 =
      r0.1.toNat * EvmWord.val256 v.1 v.2.1 v.2.2.1 v.2.2.2 +
        EvmWord.val256 r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1 +
        r0.2.2.2.2.2.toNat * 2^256 := by
  dsimp only
  unfold fullDivN1R0
  dsimp only
  have h := iterN1_fullDivN1NormV_val256_conservation_of_shape bltu_0
    b0 b1 b2 b3
    (fullDivN1NormU a0 a1 a2 a3 b0).1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    hbnz hb1z hb2z hb3z hcarry2
  dsimp only at h
  simpa using h

/-- The n=1-shaped normalized divisor equals the original divisor scaled by
    the CLZ normalization factor. -/
theorem fullDivN1NormV_val256_eq_scaled_of_shape
    (b0 b1 b2 b3 : Word)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2 =
    EvmWord.val256 b0 b1 b2 b3 * 2^(fullDivN1Shift b0).toNat := by
  subst b1
  subst b2
  subst b3
  unfold fullDivN1NormV fullDivN1AntiShift
  dsimp only
  unfold fullDivN1Shift
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b0).1.toNat % 64 = (clzResult b0).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b0; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b0)]
  exact EvmWord.val256_normalize h_shift_pos (by omega) b0 0 0 0 (by simp)

/-- The normalized dividend plus overflow limb equals the original dividend
    scaled by the n=1 CLZ normalization factor. -/
theorem fullDivN1NormU_val256_eq_scaled
    (a0 a1 a2 a3 b0 : Word) (hshift_nz : (clzResult b0).1 ≠ 0) :
    EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 +
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2^256 =
    EvmWord.val256 a0 a1 a2 a3 * 2^(fullDivN1Shift b0).toNat := by
  unfold fullDivN1NormU fullDivN1AntiShift
  dsimp only
  unfold fullDivN1Shift
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have hsmod : (clzResult b0).1.toNat % 64 = (clzResult b0).1.toNat :=
    Nat.mod_eq_of_lt (by have := clzResult_fst_toNat_le b0; omega)
  rw [hsmod, antiShift_toNat_mod_eq h_shift_pos (clzResult_fst_toNat_le b0)]
  exact EvmWord.val256_normalize_general h_shift_pos (by omega) a0 a1 a2 a3

/-- Raw Euclidean equation target for the n=1 schoolbook loop.  This is the
    unnormalized mulsub equation consumed by the legacy stack wrappers. -/
abbrev fullDivN1MulSubEq (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 =
    (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
      ((fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
      ((fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2 ^ 64 +
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

/-- Raw quotient-overestimate target for the n=1 schoolbook loop. -/
abbrev fullDivN1QuotientOverestimate (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
      ((fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
      ((fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2 ^ 64 +
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- Normalized Euclidean equation target for the n=1 schoolbook loop. The final
    normalized remainder `fullDivN1R0` is paired with all four quotient limbs. -/
abbrev fullDivN1NormalizedMulSubEq (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 * 2 ^ (fullDivN1Shift b0).toNat =
    (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
      ((fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
      ((fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2 ^ 64 +
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      (EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat) +
    EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1

/-- Raw normalized conservation equation for the n=1 final state, before
    separately proving that the final overflow carry is zero. -/
abbrev fullDivN1NormalizedConservation (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 * 2 ^ (fullDivN1Shift b0).toNat =
    (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
      ((fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
      ((fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2 ^ 64 +
      ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      (EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat) +
    EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 +
    (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat *
      2 ^ 256

/-- Normalized final-remainder bound paired with
    `fullDivN1NormalizedMulSubEq`. -/
abbrev fullDivN1NormalizedRemainderLt (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
    EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat

abbrev fullDivN1FinalCarryZero (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0

abbrev fullDivN1R3CarryZero (bltu_3 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0

abbrev fullDivN1R2CarryZero (bltu_3 bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0

abbrev fullDivN1R1CarryZero (bltu_3 bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2 = 0

private theorem fullDivN1_val256_with_overflow_eq_low_add_tail
    (u0 u1 u2 u3 u4 : Word) :
    EvmWord.val256 u0 u1 u2 u3 + u4.toNat * 2 ^ 256 =
      u0.toNat + 2 ^ 64 * EvmWord.val256 u1 u2 u3 u4 := by
  unfold EvmWord.val256
  ring

private theorem fullDivN1_four_step_conservation_nat
    {a b q3 q2 q1 q0 u0 u1 u2 u3 u4 r3 r2 r1 r0 c3 c2 c1 c0 : Nat}
    (hfirst :
      a = u0 + 2 ^ 64 * (u1 + 2 ^ 64 * (u2 + 2 ^ 64 * (u3 + 2 ^ 64 * u4))))
    (hiter3 : u3 + 2 ^ 64 * u4 = q3 * b + r3 + c3 * 2 ^ 256)
    (hc3 : c3 = 0)
    (hiter2 : u2 + 2 ^ 64 * r3 = q2 * b + r2 + c2 * 2 ^ 256)
    (hc2 : c2 = 0)
    (hiter1 : u1 + 2 ^ 64 * r2 = q1 * b + r1 + c1 * 2 ^ 256)
    (hc1 : c1 = 0)
    (hiter0 : u0 + 2 ^ 64 * r1 = q0 * b + r0 + c0 * 2 ^ 256) :
    a = (q3 * 2 ^ 192 + q2 * 2 ^ 128 + q1 * 2 ^ 64 + q0) * b + r0 +
      c0 * 2 ^ 256 := by
  subst c3
  subst c2
  subst c1
  nlinarith

/-- Assemble the four per-iteration n=1 conservation equations into the raw
    normalized conservation equation.  Intermediate carry-zero hypotheses
    remove the overflow limb from the first three iterations; the final carry
    remains in the conclusion for the later `fullDivN1NormalizedMulSubEq`
    bridge. -/
theorem fullDivN1NormalizedConservation_of_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1NormalizedConservation
  rw [← fullDivN1NormU_val256_eq_scaled a0 a1 a2 a3 b0 hshift_nz]
  rw [← fullDivN1NormV_val256_eq_scaled_of_shape b0 b1 b2 b3 hb1z hb2z hb3z hshift_nz]
  refine @fullDivN1_four_step_conservation_nat
    (EvmWord.val256
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1 +
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat * 2 ^ 256)
    (EvmWord.val256
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
    (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1.toNat
    (fullDivN1NormU a0 a1 a2 a3 b0).1.toNat
    (fullDivN1NormU a0 a1 a2 a3 b0).2.1.toNat
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1.toNat
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1.toNat
    (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2.toNat
    (EvmWord.val256
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    (EvmWord.val256
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    (EvmWord.val256
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    (EvmWord.val256
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)
    (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat
    (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat
    (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat
    (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.2.toNat
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [fullDivN1_val256_with_overflow_eq_low_add_tail]
    unfold EvmWord.val256
    ring
  · have h :=
      fullDivN1R3_val256_conservation_of_shape bltu_3
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hcarry2
    dsimp only at h
    unfold EvmWord.val256 at h
    simpa [EvmWord.val256, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  · unfold fullDivN1R3CarryZero at hr3_zero
    exact congrArg BitVec.toNat hr3_zero
  · have h :=
      fullDivN1R2_val256_conservation_of_shape bltu_3 bltu_2
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hcarry2
    dsimp only at h
    rw [fullDivN1_val256_with_overflow_eq_low_add_tail] at h
    simpa [EvmWord.val256, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  · unfold fullDivN1R2CarryZero at hr2_zero
    exact congrArg BitVec.toNat hr2_zero
  · have h :=
      fullDivN1R1_val256_conservation_of_shape bltu_3 bltu_2 bltu_1
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hcarry2
    dsimp only at h
    rw [fullDivN1_val256_with_overflow_eq_low_add_tail] at h
    simpa [EvmWord.val256, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  · unfold fullDivN1R1CarryZero at hr1_zero
    exact congrArg BitVec.toNat hr1_zero
  · have h :=
      fullDivN1R0_val256_conservation_of_shape bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 hbnz hb1z hb2z hb3z hcarry2
    dsimp only at h
    rw [fullDivN1_val256_with_overflow_eq_low_add_tail] at h
    simpa [EvmWord.val256, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- Drop the final overflow term from normalized n=1 conservation once its
    carry is known to be zero. -/
theorem fullDivN1NormalizedMulSubEq_of_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcons : fullDivN1NormalizedConservation bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hcarry_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold fullDivN1NormalizedConservation at hcons
  unfold fullDivN1FinalCarryZero at hcarry_zero
  unfold fullDivN1NormalizedMulSubEq
  rw [hcarry_zero] at hcons
  simpa using hcons

/-- Direct normalized mulsub bridge from the four n=1 step-conservation
    equations and all carry-zero hypotheses. -/
theorem fullDivN1NormalizedMulSubEq_of_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  exact fullDivN1NormalizedMulSubEq_of_conservation bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3
    (fullDivN1NormalizedConservation_of_step_conservation
      bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      hbnz hb1z hb2z hb3z hshift_nz hcarry2 hr3_zero hr2_zero hr1_zero)
    hfinal_zero

/-- Raw dispatcher-surface carry form of
    `fullDivN1NormalizedMulSubEq_of_step_conservation`. -/
theorem fullDivN1NormalizedMulSubEq_of_raw_step_conservation
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (hcarry2 : Carry2NzAll (b0 <<< (((clzResult b0).1).toNat % 64))
      ((b1 <<< (((clzResult b0).1).toNat % 64)) |||
        (b0 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b2 <<< (((clzResult b0).1).toNat % 64)) |||
        (b1 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64)))
      ((b3 <<< (((clzResult b0).1).toNat % 64)) |||
        (b2 >>> ((signExtend12 (0 : BitVec 12) -
          (clzResult b0).1).toNat % 64))))
    (hr3_zero : fullDivN1R3CarryZero bltu_3 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr2_zero : fullDivN1R2CarryZero bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (hr1_zero : fullDivN1R1CarryZero bltu_3 bltu_2 bltu_1
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hfinal_zero : fullDivN1FinalCarryZero bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hcarry2Norm : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2 := by
    unfold fullDivN1NormV fullDivN1Shift fullDivN1AntiShift
    rw [fullDivN1Shift_unfold]
    exact hcarry2
  exact fullDivN1NormalizedMulSubEq_of_step_conservation
    bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz hcarry2Norm
    hr3_zero hr2_zero hr1_zero hfinal_zero

/-- n=1 quotient bridge from the normalized Euclidean equation and normalized
    final-remainder bound. -/
theorem fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q2 := (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q3 := (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1
  have hq_norm :
      q3.toNat * 2 ^ 192 + q2.toNat * 2 ^ 128 + q1.toNat * 2 ^ 64 + q0.toNat =
        EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 :=
    EvmWord.div_quotient_of_normalized
      (s := (fullDivN1Shift b0).toNat) hmulsub hrem_lt
  have hq_val :
      EvmWord.val256 q0 q1 q2 q3 =
        EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 := by
    exact EvmWord.accumulated_eq_val256_n1.symm.trans hq_norm
  have hdiv := EvmWord.div_of_val256_eq_div
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (q2 := q2) (q3 := q3) hbnz hq_val
  delta fullDivN1QuotientWord
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => q3) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact hdiv

/-- Normalized n=1 Euclidean facts imply the legacy quotient-overestimate
    shape expected by dispatcher wrappers. -/
theorem fullDivN1QuotientOverestimate_of_normalized_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
      ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
        ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
        ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
        ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat := by
  exact le_of_eq
    (EvmWord.div_quotient_of_normalized
      (s := (fullDivN1Shift b0).toNat) hmulsub hrem_lt).symm

/-- The normalized n=1 Euclidean equation plus the legacy quotient
    overestimate gives the normalized final-remainder bound. -/
theorem fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  have hbpos : 0 < EvmWord.val256 b0 b1 b2 b3 :=
    EvmWord.val256_pos_of_or_ne_zero hbnz
  have hpow : 0 < 2 ^ (fullDivN1Shift b0).toNat := by
    positivity
  have hbScaled : 0 <
      EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat := by
    positivity
  have hgeScaled :
      (EvmWord.val256 a0 a1 a2 a3 * 2 ^ (fullDivN1Shift b0).toNat) /
        (EvmWord.val256 b0 b1 b2 b3 * 2 ^ (fullDivN1Shift b0).toNat) ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat := by
    rw [Nat.mul_div_mul_right _ _ hpow]
    exact hge
  exact (EvmWord.remainder_lt_of_ge_floor hbScaled hmulsub hgeScaled).2

/-- n=1 quotient bridge from normalized mulsub plus the legacy quotient
    overestimate. -/
theorem fullDivN1QuotientWord_eq_div_of_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  exact fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub
    (fullDivN1NormalizedRemainderLt_of_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge)

/-- n=1 normalized quotient bridge specialized to the explicit limb variables
    used by the unified-bound wrappers. -/
theorem fullDivN1QuotientWord_eq_div_of_limbs_normalized_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2 ^ 64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  have hraw :=
    fullDivN1QuotientWord_eq_div_of_normalized_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- n=1 quotient bridge specialized to branch constructors that store
    `a`/`b` as `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  have hraw :=
    fullDivN1QuotientWord_eq_div_of_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- Word-specialized n=1 quotient bridge using the compact raw path aliases. -/
theorem fullDivN1QuotientWord_eq_div_of_getLimbN_path_conditions
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub : fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge : fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b :=
  fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge

/-- n=1 quotient bridge specialized to `getLimbN` call sites, using the final
    remainder bound instead of an explicit quotient-overestimate hypothesis. -/
theorem fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hrem_lt :
      EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1) <
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  have hraw :=
    fullDivN1QuotientWord_eq_div_of_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt
  change
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) at hraw
  exact hraw.trans (by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b)

/-- n=1 quotient bridge specialized to the explicit limb variables used by the
    unified-bound wrappers. -/
theorem fullDivN1QuotientWord_eq_div_of_limbs_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  exact fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge

/-- Explicit-limb n=1 four-limb division witness using the legacy
    quotient-overestimate hypothesis. -/
theorem fullDivN1_getLimbN_of_limbs_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- n=1 four-limb division witness specialized to `getLimbN` call sites,
    using the legacy quotient-overestimate hypothesis. -/
theorem fullDivN1_getLimbN_of_getLimbN_mulsub_overestimate
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  exact fullDivN1_getLimbN_of_limbs_mulsub_overestimate
    bltu_3 bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hge

/-- Explicit-limb n=1 quotient bridge using the final remainder bound. -/
theorem fullDivN1QuotientWord_eq_div_of_limbs_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hrem_lt :
      EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1) <
        EvmWord.val256 b0 b1 b2 b3) :
    fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  exact fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt

/-- Explicit-limb n=1 four-limb division witness using the final
    remainder bound. -/
theorem fullDivN1_getLimbN_of_limbs_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hrem_lt :
      EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1) <
        EvmWord.val256 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_limbs_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hrem_lt
  exact fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- n=1 four-limb division witness specialized to `getLimbN` call sites,
    using the final remainder bound. -/
theorem fullDivN1_getLimbN_of_getLimbN_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN1R3 bltu_3
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^192 +
          ((fullDivN1R2 bltu_3 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN1R1 bltu_3 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hrem_lt :
      EvmWord.val256
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1) <
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  exact fullDivN1_getLimbN_of_limbs_mulsub_remainder_lt
    bltu_3 bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hrem_lt

/-- Explicit-limb n=1 four-limb division witness from normalized Euclidean
    facts. -/
theorem fullDivN1_getLimbN_of_limbs_normalized_mulsub_remainder_lt
    (bltu_3 bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN1NormalizedMulSubEq bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hrem_lt : fullDivN1NormalizedRemainderLt bltu_3 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN1R1 bltu_3 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN1R2 bltu_3 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 =
      (fullDivN1R3 bltu_3 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_normalized_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt
  have hfold :
      EvmWord.div
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => a.getLimbN 0
            | 1 => a.getLimbN 1
            | 2 => a.getLimbN 2
            | 3 => a.getLimbN 3)
          (EvmWord.fromLimbs fun i : Fin 4 =>
            match i with
            | 0 => b.getLimbN 0
            | 1 => b.getLimbN 1
            | 2 => b.getLimbN 2
            | 3 => b.getLimbN 3) =
        EvmWord.div a b := by
    congr
    · exact EvmWord.fromLimbs_match_getLimbN_id a
    · exact EvmWord.fromLimbs_match_getLimbN_id b
  have hdivWord' := hdivWord.trans hfold
  exact fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
    a b (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hdivWord'


end EvmAsm.Evm64
