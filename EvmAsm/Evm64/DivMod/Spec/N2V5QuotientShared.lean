/- Shared declaration home for the n=2 V5 quotient-shape arithmetic. -/

import EvmAsm.Evm64.DivMod.Spec.N2V5FamiliesShapeShared
import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

/-- Pack the three per-limb v5 n=2 DIV results into a single `EvmWord` (top
    limb `0`). -/
@[irreducible]
def fullDivN2QuotientWordV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 1 => (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 2 => (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
    | 3 => (0 : Word))

theorem fullDivN2QuotientWordV5_getLimbN0 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 0
    = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0

theorem fullDivN2QuotientWordV5_getLimbN1 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 1
    = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1

theorem fullDivN2QuotientWordV5_getLimbN2 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 2
    = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2

theorem fullDivN2QuotientWordV5_getLimbN3 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    (fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).getLimbN 3
    = (0 : Word) := by
  delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3


open EvmAsm.Rv64
open EvmWord

theorem fullDivN2QuotientWordV5_eq_div_of_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q2 := (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n2_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (q2 := q2)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [q0, q1, q2, r0, r1, r2, r3] using hmulsub)
    (by simpa [q0, q1, q2] using hge)
  delta fullDivN2QuotientWordV5
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => q0 | 1 => q1 | 2 => q2 | 3 => (0 : Word)) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1


open EvmAsm.Rv64
open EvmWord

theorem fullDivN2QuotientWordV5_eq_div_lane
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
      = EvmWord.div a b := by
  have hraw := fullDivN2QuotientWordV5_eq_div_of_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

/-- Per-limb form: each limb of `EvmWord.div a b` equals the corresponding v5
    n=2 schoolbook digit (limb 3 is `0`). -/
theorem div_getLimbN_eq_digit_n2_v5
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      val256 a0 a1 a2 a3 =
        (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          val256 b0 b1 b2 b3 +
        val256
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hw := fullDivN2QuotientWordV5_eq_div_lane bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [← hw]
  · exact fullDivN2QuotientWordV5_getLimbN0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN1 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN2 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3
  · exact fullDivN2QuotientWordV5_getLimbN3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3


open EvmAsm.Rv64
open EvmWord

/-- v5 n=2 per-digit conservation (mulsub) predicate: `val256 a = q·val256 b + r`
    for the assembled v5 n=2 quotient/remainder. -/
abbrev fullDivN2MulSubEqV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  val256 a0 a1 a2 a3 =
    (((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
      ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      val256 b0 b1 b2 b3 +
    val256
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

/-- v5 n=2 quotient lower-bound (overestimate) predicate: `a/b ≤` the assembled
    v5 n=2 quotient. -/
abbrev fullDivN2QuotientOverestimateV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤
    ((fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
      ((fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- The lane's `a b : EvmWord` div limbs equal the v5 n=2 digits, from the
    packaged conditions. -/
theorem div_getLimbN_eq_digit_n2_v5_of_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  div_getLimbN_eq_digit_n2_v5 bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge


open EvmAsm.Rv64

/-- v5 n=2 trial branch, j=2 (top digit): call iff `uTop < v.2.1`. -/
def isTrialN2V5_j2 (bltu_2 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_2 =
    BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- v5 n=2 trial branch, j=1: call iff the j=2 remainder's limb1 `< v.2.1`. -/
def isTrialN2V5_j1 (bltu_2 bltu_1 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_1 =
    BitVec.ult
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- v5 n=2 trial branch, j=0: call iff the j=1 remainder's limb1 `< v.2.1`. -/
def isTrialN2V5_j0 (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 =
    BitVec.ult
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- Bundled v5 n=2 path predicate: the three trial branches plus the conservation
    and quotient-overestimate facts.  The v5 n=2 loop establishes this; the
    quotient correctness consumes the last two conjuncts. -/
def fullDivN2PathConditionsV5 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN2V5_j2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V5_j1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V5_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

theorem fullDivN2PathConditionsV5_mulsub
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2MulSubEqV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.1

theorem fullDivN2PathConditionsV5_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientOverestimateV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.2

/-- EvmWord-level v5 n=2 quotient bridge from the bundled path predicate. -/
theorem div_getLimbN_eq_digit_n2_v5_of_path
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN2PathConditionsV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  div_getLimbN_eq_digit_n2_v5_of_conditions bltu_2 bltu_1 bltu_0
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz
    (fullDivN2PathConditionsV5_mulsub bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath)
    (fullDivN2PathConditionsV5_overestimate bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath)


open EvmWord EvmAsm.Rv64

/-- **v5 n=2 quotient correctness (shift≠0), from shape + `bltu` path matches.**
    The assembled v5 n=2 quotient word equals `EvmWord.div a b`. -/
theorem fullDivN2QuotientWordV5_eq_div_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  have h0 : (0:Word).toNat = 0 := rfl
  have hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0 := by
    intro h
    have h2 := (BitVec.or_eq_zero_iff.mp h).1
    have h3 := (BitVec.or_eq_zero_iff.mp h2).1
    exact hb1nz (BitVec.or_eq_zero_iff.mp h3).2
  have hacc := fullDivN2_acc_quot_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3
    bltu_2 bltu_1 bltu_0 hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  have hqval : val256 (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
      (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 0
      = val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 := by
    rw [← hacc]; simp only [EvmWord.val256, h0]; ring
  have hdiv := div_of_val256_eq_div hbnz hqval
  unfold fullDivN2QuotientWordV5
  exact hdiv

/-- **getLimbN bridge.** Decompose the quotient-word equality into the four
    per-limb `getLimbN`/digit equalities the n=2 lane wrapper feeds to
    `divStackDispatchPost`.  Pure `fromLimbs` projection — n=2 analog of
    `fullDivN1V5_hdivs_of_word_eq`. -/
theorem fullDivN2V5_hdivs_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hdiv : fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]; delta fullDivN2QuotientWordV5; exact EvmWord.getLimbN_fromLimbs_3

/-- **Lane-ready form: the four `(div a b).getLimbN` digit equalities from shape**
    (shift≠0) + the `bltu` path matches.  Composes
    `fullDivN2QuotientWordV5_eq_div_of_shape` with the `getLimbN` bridge. -/
theorem div_getLimbN_eq_digit_n2_v5_of_shape
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1
      = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2
      = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3
      = (0 : Word) :=
  fullDivN2V5_hdivs_of_word_eq _ _ a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0
    (fullDivN2QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0
      hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0)

/-- **Lane bridge from the path predicate's trial branches.** The four
    `(div a b).getLimbN` digit equalities from shape (shift≠0) + the three v5 n=2
    trial-branch predicates `isTrialN2V5_j{2,1,0}` (which the loop establishes).
    Derives the `bltu` path matches from the trial branches and applies
    `div_getLimbN_eq_digit_n2_v5_of_shape`.  This is the corrected (shift-aware)
    counterpart of `div_getLimbN_eq_digit_n2_v5_of_path`, free of the mis-stated
    `fullDivN2MulSubEqV5`. -/
theorem div_getLimbN_eq_digit_n2_v5_of_trials
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) (bltu_2 bltu_1 bltu_0 : Bool)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (ht2 : isTrialN2V5_j2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3)
    (ht1 : isTrialN2V5_j1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3)
    (ht0 : isTrialN2V5_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 0
      = (fullDivN2R0V5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 1
      = (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 2
      = (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 => match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)).getLimbN 3
      = (0 : Word) := by
  unfold isTrialN2V5_j2 at ht2
  unfold isTrialN2V5_j1 at ht1
  unfold isTrialN2V5_j0 at ht0
  exact div_getLimbN_eq_digit_n2_v5_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0
    hb2z hb3z hshift_nz hb1nz
    (fun h => ht2.symm.trans h) (fun h hu => by rw [h] at ht2; rw [hu] at ht2; exact absurd ht2 (by decide))
    (fun h => ht1.symm.trans h) (fun h hu => by rw [h] at ht1; rw [hu] at ht1; exact absurd ht1 (by decide))
    (fun h => ht0.symm.trans h) (fun h hu => by rw [h] at ht0; rw [hu] at ht0; exact absurd ht0 (by decide))


open EvmAsm.Rv64

/-- Lane form from shape: the assembled v5 n=2 quotient word equals `EvmWord.div a b`. -/
theorem fullDivN2QuotientWordV5_eq_div_lane_of_shape
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hb2z : b2 = 0) (hb3z : b3 = 0) (hshift_nz : (clzResult b1).1 ≠ 0) (hb1nz : b1 ≠ 0)
    (hc2 : bltu_2 = true → BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm2 : bltu_2 = false → ¬ BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc1 : bltu_1 = true → BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm1 : bltu_1 = false → ¬ BitVec.ult (fullDivN2R2V5 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1)
    (hc0 : bltu_0 = true → BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1 = true)
    (hm0 : bltu_0 = false → ¬ BitVec.ult (fullDivN2R1V5 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1 (fullDivN2NormV b0 b1 b2 b3).2.1) :
    fullDivN2QuotientWordV5 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  have hraw := fullDivN2QuotientWordV5_eq_div_of_shape a0 a1 a2 a3 b0 b1 b2 b3 bltu_2 bltu_1 bltu_0
    hb2z hb3z hshift_nz hb1nz hc2 hm2 hc1 hm1 hc0 hm0
  subst a0; subst a1; subst a2; subst a3; subst b0; subst b1; subst b2; subst b3
  refine hraw.trans ?_
  congr 1
  · exact EvmWord.fromLimbs_match_getLimbN_id a
  · exact EvmWord.fromLimbs_match_getLimbN_id b

end EvmAsm.Evm64
