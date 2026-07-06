/-
  EvmAsm.Evm64.DivMod.Spec.N1V5ModRemainder

  **v5 n=1 MOD remainder correctness from shape (shift≠0):**
  `fullModN1RemainderWordV5 = EvmWord.mod a b`.

  The n=1 analog of `fullModN2RemainderWordV5_eq_mod_of_shape` (N2V5ModRemainder).
  For the single-limb divisor case (b1=b2=b3=0) the normalized remainder collapses
  to one limb (`val256_high_limbs_zero_of_lt_word` applied to the R0 remainder
  bound), so the denormalized remainder word reduces to the single-limb form
  `fromLimbs [R0.2.1 >>> shift, 0, 0, 0]` proven equal to `EvmWord.mod a b` by
  `fullDivN1V5_remainder_eq_mod_of_shape` (N1V5Quotient).  Bead `evm-asm-wbc4i.9.1`.
-/

import EvmAsm.Evm64.DivMod.Spec.N1V5Quotient
import EvmAsm.Evm64.DivMod.Spec.N1CarryZeroReducers

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Pack the four denormalized v5 n=1 MOD remainder limbs (funnel-shift-down of
    `fullDivN1R0V5`'s remainder by `fullDivN1Shift b0`) into a single `EvmWord`.
    Matches the `denormModPost` limb formulas exactly. -/
@[irreducible]
def fullModN1RemainderWordV5 (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 =>
        ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))
    | 1 =>
        ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))
    | 2 =>
        ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>>
            ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<<
            ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))
    | 3 =>
        (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>>
          ((fullDivN1Shift b0).toNat % 64))

/-- **v5 n=1 MOD remainder correctness (shift≠0), from shape.**
    `fullModN1RemainderWordV5 = EvmWord.mod a b`. -/
theorem fullModN1RemainderWordV5_eq_mod_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    fullModN1RemainderWordV5 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.mod
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  -- single-limb collapse: the high remainder limbs are zero
  have hlt := fullDivN1R0V5_remainder_lt_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz
  obtain ⟨h1, h2, h3⟩ := val256_high_limbs_zero_of_lt_word
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
    (fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
    (fullDivN1NormV b0 b1 b2 b3).1 hlt
  -- shift < 64 so `% 64` is identity
  have hslt : (fullDivN1Shift b0).toNat % 64 = (fullDivN1Shift b0).toNat := by
    apply Nat.mod_eq_of_lt
    have := clzResult_fst_toNat_le b0
    unfold fullDivN1Shift; omega
  refine Eq.trans ?_ (fullDivN1V5_remainder_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz)
  unfold fullModN1RemainderWordV5
  rw [h1, h2, h3, hslt]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Per-limb projection of the n=1 MOD remainder word equality. -/
theorem fullModN1V5_hmods_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hmod : fullModN1RemainderWordV5 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b) :
    (EvmWord.mod a b).getLimbN 0 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 1 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 2 =
        (((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1 >>> ((fullDivN1Shift b0).toNat % 64)) |||
          ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <<< ((signExtend12 (0 : BitVec 12) - fullDivN1Shift b0).toNat % 64))) ∧
    (EvmWord.mod a b).getLimbN 3 =
        ((fullDivN1R0V5 true true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 >>> ((fullDivN1Shift b0).toNat % 64)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmod]; delta fullModN1RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hmod]; delta fullModN1RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hmod]; delta fullModN1RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hmod]; delta fullModN1RemainderWordV5; exact EvmWord.getLimbN_fromLimbs_3

/-- Lane form from shape: the assembled v5 n=1 remainder word equals `EvmWord.mod a b`. -/
theorem fullModN1RemainderWordV5_eq_mod_lane_of_shape
    {a b : EvmWord} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb1z : b1 = 0) (hb2z : b2 = 0) (hb3z : b3 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    fullModN1RemainderWordV5 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.mod a b := by
  have hraw := fullModN1RemainderWordV5_eq_mod_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    hbnz hb1z hb2z hb3z hshift_nz
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

end EvmAsm.Evm64
