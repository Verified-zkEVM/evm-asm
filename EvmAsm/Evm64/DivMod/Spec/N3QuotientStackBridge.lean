/-
  EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge

  Explicit-limb n=3 quotient bridge for Unified stack wrapper call sites.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3QuotientWord
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def isTrialN3V4_j1 (bltu : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu =
    BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      (fullDivN3NormV b0 b1 b2 b3).2.2.1

def isTrialN3V4_j0 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 =
    if bltu_1 then
      BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
    else
      BitVec.ult
        (iterN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1

abbrev fullDivN3MulSubEqV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 =
    (((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^64 +
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

abbrev fullDivN3QuotientOverestimateV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    ((fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^64 +
      ((fullDivN3R0V4 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- Legacy universal n=3 carry package.

    This expands to raw `Carry2NzAll` over the normalized divisor. It is
    counterexample-false as a final/public proof surface, because it quantifies
    over carry facts for branch states that need not be reachable by the actual
    selected v4 path. New stack/callable work should use
    `fullDivN3SelectedCarryV4` instead. -/
abbrev fullDivN3Carry2NzV4 (b0 b1 b2 b3 : Word) : Prop :=
  Carry2NzAll (fullDivN3NormV b0 b1 b2 b3).1
    (fullDivN3NormV b0 b1 b2 b3).2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.1
    (fullDivN3NormV b0 b1 b2 b3).2.2.2

/-- Legacy bundled n=3 v4 path predicate.

    This retains `fullDivN3Carry2NzV4`, so it is only a compatibility shim for
    older callers. Use `fullDivN3SelectedPathConditionsV4` for new v4
    stack/callable wrappers. -/
abbrev fullDivN3PathConditionsV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN3V4_j1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN3V4_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3Carry2NzV4 b0 b1 b2 b3 ∧
  fullDivN3MulSubEqV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3QuotientOverestimateV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

/-- Selected per-iteration carry facts for the n=3 V4 path.

    This is the replacement surface for the false universal
    `fullDivN3Carry2NzV4` package: it asks only for the carry fact selected by
    each concrete branch boolean and by the actual intermediate `u` state. -/
abbrev fullDivN3SelectedCarryV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN3NormV b0 b1 b2 b3
  let u := fullDivN3NormU a0 a1 a2 a3 b2
  let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  (if bltu_1 then
    loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)
   else
    isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)) ∧
  (if bltu_0 then
    loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
   else
    isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)

/-- Selected-carry n=3 V4 path predicate. Unlike
    `fullDivN3PathConditionsV4`, this contains no `Carry2NzAll` component. -/
abbrev fullDivN3SelectedPathConditionsV4 (bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN3V4_j1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN3V4_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3SelectedCarryV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3MulSubEqV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN3QuotientOverestimateV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

/-- First selected n=3 carry component, for the `j=1` loop iteration. -/
theorem fullDivN3SelectedCarryV4_j1
    (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcarry : fullDivN3SelectedCarryV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    if bltu_1 then
      loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)
    else
      isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) :=
  hcarry.1

/-- Second selected n=3 carry component, for the `j=0` loop iteration. -/
theorem fullDivN3SelectedCarryV4_j0
    (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcarry : fullDivN3SelectedCarryV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN3NormV b0 b1 b2 b3
    let u := fullDivN3NormU a0 a1 a2 a3 b2
    let r1 := fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    if bltu_0 then
      loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 :=
  hcarry.2

/-- Project the v4 N3 normalized mulsub equation from the bundled explicit-limb path. -/
theorem fullDivN3PathConditionsV4_mulsub
    (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN3PathConditionsV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3MulSubEqV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.1

/-- Project the v4 N3 quotient-overestimate fact from the bundled explicit-limb path. -/
theorem fullDivN3PathConditionsV4_overestimate
    (bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN3PathConditionsV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3QuotientOverestimateV4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.2

abbrev fullDivN3PathConditionsWordV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3PathConditionsV4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

abbrev fullDivN3SelectedPathConditionsWordV4 (bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN3SelectedPathConditionsV4 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Project the first v4 N3 trial-branch witness from the bundled word path. -/
theorem fullDivN3PathConditionsWordV4_trial_j1
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    isTrialN3V4_j1 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.1

/-- Project the second v4 N3 trial-branch witness from the bundled word path. -/
theorem fullDivN3PathConditionsWordV4_trial_j0
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    isTrialN3V4_j0 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.1

/-- Project the v4 N3 carry2 obligation from the bundled word path. -/
theorem fullDivN3PathConditionsWordV4_carry2
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.1

/-- Project the v4 N3 normalized mulsub equation from the bundled word path. -/
theorem fullDivN3PathConditionsWordV4_mulsub
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3MulSubEqV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  fullDivN3PathConditionsV4_mulsub bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hpath

/-- Project the v4 N3 quotient-overestimate fact from the bundled word path. -/
theorem fullDivN3PathConditionsWordV4_overestimate
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  fullDivN3PathConditionsV4_overestimate bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hpath

/-- Project the selected carry package from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_selectedCarry
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3SelectedCarryV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.1

/-- Project the first selected n=3 carry component from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_carry_j1
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    let v := fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)
    let u := fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)
    if bltu_1 then
      loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word)
    else
      isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) :=
  fullDivN3SelectedCarryV4_j1 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (fullDivN3SelectedPathConditionsWordV4_selectedCarry
      bltu_1 bltu_0 a b hpath)

/-- Project the second selected n=3 carry component from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_carry_j0
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    let v := fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)
    let u := fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)
    let r1 := fullDivN3R1V4 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    if bltu_0 then
      loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 :=
  fullDivN3SelectedCarryV4_j0 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (fullDivN3SelectedPathConditionsWordV4_selectedCarry
      bltu_1 bltu_0 a b hpath)

/-- Expanded selected n=3 carry component for the `j=0` loop iteration.
    This is the older stack-wrapper shape, where the `j=1` intermediate state
    is exposed by case-splitting on the first trial branch. -/
abbrev fullDivN3SelectedCarryJ0ExpandedWordV4
    (bltu_1 bltu_0 : Bool) (a b : EvmWord) : Prop :=
  match bltu_1 with
  | false =>
    let r1 := iterN3Max
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
      (0 : Word)
    if bltu_0 then
      loopBodyN3CallAddbackCarry2NzV4
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN3Max
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  | true =>
    let r1 := iterWithDoubleAddback
      (divKTrialCallV4QHat
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
      (0 : Word)
    if bltu_0 then
      loopBodyN3CallAddbackCarry2NzV4
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN3Max
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- `fullDivN3R1V4`-shaped selected n=3 carry component for the `j=0`
    loop iteration. This is the shape projected from the selected path
    package. -/
abbrev fullDivN3SelectedCarryJ0R1WordV4
    (bltu_1 bltu_0 : Bool) (a b : EvmWord) : Prop :=
  let v := fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
    (b.getLimbN 2) (b.getLimbN 3)
  let u := fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
    (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)
  let r1 := fullDivN3R1V4 bltu_1
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  if bltu_0 then
    loopBodyN3CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  else
    isAddbackCarry2NzN3Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1

/-- Project the first v4 N3 trial-branch witness from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_trial_j1
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    isTrialN3V4_j1 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.1

/-- Project the second v4 N3 trial-branch witness from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_trial_j0
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    isTrialN3V4_j0 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.1

/-- Project the v4 N3 normalized mulsub equation from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_mulsub
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3MulSubEqV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.1

/-- Project the v4 N3 quotient-overestimate fact from the selected-carry word path. -/
theorem fullDivN3SelectedPathConditionsWordV4_overestimate
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.2

/-- n=3 quotient bridge specialized to the explicit limb variables used by the
    unified-bound wrappers. -/
theorem fullDivN3QuotientWord_eq_div_of_limbs_mulsub_overestimate
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN3R1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
            2^64 +
          ((fullDivN3R0 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN3QuotientWord bltu_1 bltu_0
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
    fullDivN3QuotientWord_eq_div_of_mulsub_overestimate
      bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN3QuotientWord bltu_1 bltu_0
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

/-- Explicit-limb n=3 quotient bridge for the v4 call/max path. -/
theorem fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN3MulSubEqV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
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
    fullDivN3QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN3QuotientWordV4 bltu_1 bltu_0
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

/-- Explicit-limb n=3 v4 four-limb division witness using the legacy
    quotient-overestimate hypothesis. -/
theorem fullDivN3V4_getLimbN_of_limbs_mulsub_overestimate
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN3MulSubEqV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hdivWord :=
    fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
      bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge
  exact fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- Explicit-limb v4 quotient bridge from the bundled N3 path predicate. -/
theorem fullDivN3QuotientWordV4_eq_div_of_path_conditions
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN3PathConditionsV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  have hmulsub := fullDivN3PathConditionsV4_mulsub
    bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  have hge := fullDivN3PathConditionsV4_overestimate
    bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  exact fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
    bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge

/-- EvmWord-level v4 quotient bridge from the bundled N3 path predicate. -/
theorem fullDivN3QuotientWordV4_eq_div_of_word_path_conditions
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN3QuotientWordV4_eq_div_of_path_conditions
    bltu_1 bltu_0 (a := a) (b := b)
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz hpath

/-- EvmWord-level v4 quotient bridge from the bundled N3 path predicate,
    accepting the public `b ≠ 0` nonzero form. -/
theorem fullDivN3QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN3QuotientWordV4_eq_div_of_word_path_conditions
    bltu_1 bltu_0 a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hpath

/-- EvmWord-level v4 quotient bridge from the selected-carry N3 path predicate.

    This avoids the false `fullDivN3Carry2NzV4`/`Carry2NzAll` package: quotient
    correctness only needs the selected path's mulsub equation and
    quotient-overestimate fact. -/
theorem fullDivN3QuotientWordV4_eq_div_of_selected_word_path_conditions
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN3QuotientWordV4_eq_div_of_limbs_mulsub_overestimate
    bltu_1 bltu_0
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz
    (fullDivN3SelectedPathConditionsWordV4_mulsub bltu_1 bltu_0 a b hpath)
    (fullDivN3SelectedPathConditionsWordV4_overestimate bltu_1 bltu_0 a b hpath)

/-- EvmWord-level v4 quotient bridge from the selected-carry N3 path predicate,
    accepting the public `b ≠ 0` nonzero form. -/
theorem fullDivN3QuotientWordV4_eq_div_of_selected_word_path_conditions_ne_zero
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hpath : fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b) :
    fullDivN3QuotientWordV4 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN3QuotientWordV4_eq_div_of_selected_word_path_conditions
    bltu_1 bltu_0 a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hpath

/-- Explicit-limb v4 four-limb division witness from the bundled N3 path
    predicate. -/
theorem fullDivN3V4_getLimbN_of_path_conditions
    (bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN3PathConditionsV4 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hmulsub := fullDivN3PathConditionsV4_mulsub
    bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  have hge := fullDivN3PathConditionsV4_overestimate
    bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  exact fullDivN3V4_getLimbN_of_limbs_mulsub_overestimate
    bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hmulsub hge

/-- EvmWord-level v4 four-limb division witness from the bundled N3 path
    predicate. -/
theorem fullDivN3V4_getLimbN_of_word_path_conditions
    (bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN3R0V4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  exact fullDivN3V4_getLimbN_of_path_conditions
    bltu_1 bltu_0 (a := a) (b := b)
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz hpath

end EvmAsm.Evm64
