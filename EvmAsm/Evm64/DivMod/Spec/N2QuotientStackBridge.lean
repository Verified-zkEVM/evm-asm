/-
  EvmAsm.Evm64.DivMod.Spec.N2QuotientStackBridge

  Explicit-limb n=2 quotient bridge for Unified stack wrapper call sites.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2QuotientWord
public import EvmAsm.Evm64.DivMod.Compose.FullPathN2V4Families
public import EvmAsm.Evm64.EvmWordArith.DivAccumulate
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord

abbrev fullDivN2MulSubEqV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 =
    (((fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^128 +
      ((fullDivN2R1V4 bltu_2 bltu_1
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1)

abbrev fullDivN2QuotientOverestimateV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    ((fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat *
        2^128 +
      ((fullDivN2R1V4 bltu_2 bltu_1
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
      ((fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3).1).toNat

/-- Legacy universal n=2 carry package.

    This expands to raw `Carry2NzAll` over the normalized divisor. It is
    counterexample-false as a final/public proof surface, because it quantifies
    over carry facts for branch states that need not be reachable by the actual
    selected v4 path. New stack/callable work should use
    `fullDivN2SelectedCarryV4` instead. -/
abbrev fullDivN2Carry2NzV4 (b0 b1 b2 b3 : Word) : Prop :=
  Carry2NzAll (fullDivN2NormV b0 b1 b2 b3).1
    (fullDivN2NormV b0 b1 b2 b3).2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.1
    (fullDivN2NormV b0 b1 b2 b3).2.2.2

def isTrialN2V4_j2 (bltu_2 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_2 =
    BitVec.ult (fullDivN2NormU a0 a1 a2 a3 b1).2.2.2.2
      (fullDivN2NormV b0 b1 b2 b3).2.1

def isTrialN2V4_j1 (bltu_2 bltu_1 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_1 =
    BitVec.ult
      (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

def isTrialN2V4_j0 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  bltu_0 =
    BitVec.ult
      (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
      (fullDivN2NormV b0 b1 b2 b3).2.1

/-- Legacy bundled n=2 v4 path predicate.

    This retains `fullDivN2Carry2NzV4`, so it is only a compatibility shim for
    older callers. Use `fullDivN2SelectedPathConditionsV4` for new v4
    stack/callable wrappers. -/
abbrev fullDivN2PathConditionsV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN2V4_j2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V4_j1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V4_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2Carry2NzV4 b0 b1 b2 b3 ∧
  fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

/-- Selected per-iteration carry facts for the n=2 V4 path.

    This is the replacement surface for the false universal
    `fullDivN2Carry2NzV4` package: it asks only for the carry fact selected by
    each concrete branch boolean and by the actual intermediate `u` state. -/
abbrev fullDivN2SelectedCarryV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN2NormV b0 b1 b2 b3
  let u := fullDivN2NormU a0 a1 a2 a3 b1
  let r2 := fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
  let r1 := fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
  (if bltu_2 then
    loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)
   else
    isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)) ∧
  (if bltu_1 then
    loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1) ∧
  (if bltu_0 then
    loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
   else
    isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
      u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1)

/-- Selected-carry n=2 V4 path predicate. Unlike
    `fullDivN2PathConditionsV4`, this contains no `Carry2NzAll` component. -/
abbrev fullDivN2SelectedPathConditionsV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  isTrialN2V4_j2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V4_j1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  isTrialN2V4_j0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3

/-- First selected n=2 carry component, for the `j=2` loop iteration. -/
theorem fullDivN2SelectedCarryV4_j2
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcarry : fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    if bltu_2 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) :=
  hcarry.1

/-- Second selected n=2 carry component, for the `j=1` loop iteration. -/
theorem fullDivN2SelectedCarryV4_j1
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcarry : fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r2 := fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3
    if bltu_1 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 :=
  hcarry.2.1

/-- Third selected n=2 carry component, for the `j=0` loop iteration. -/
theorem fullDivN2SelectedCarryV4_j0
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hcarry : fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    let v := fullDivN2NormV b0 b1 b2 b3
    let u := fullDivN2NormU a0 a1 a2 a3 b1
    let r1 := fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3
    if bltu_0 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 :=
  hcarry.2.2

/-- Project the v4 N2 normalized mulsub equation from the bundled explicit-limb path. -/
theorem fullDivN2PathConditionsV4_mulsub
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.2.1

/-- Project the v4 N2 quotient-overestimate fact from the bundled explicit-limb path. -/
theorem fullDivN2PathConditionsV4_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hpath : fullDivN2PathConditionsV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 :=
  hpath.2.2.2.2.2

abbrev fullDivN2PathConditionsWordV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN2PathConditionsV4 bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

abbrev fullDivN2SelectedPathConditionsWordV4 (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) : Prop :=
  fullDivN2SelectedPathConditionsV4 bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Project the first v4 N2 trial-branch witness from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_trial_j2
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j2 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.1

/-- Project the second v4 N2 trial-branch witness from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_trial_j1
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j1 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.1

/-- Project the third v4 N2 trial-branch witness from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_trial_j0
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.1

/-- Project the v4 N2 carry2 obligation from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_carry2
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.1

/-- Project the v4 N2 normalized mulsub equation from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_mulsub
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  fullDivN2PathConditionsV4_mulsub bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hpath

/-- Project the v4 N2 quotient-overestimate fact from the bundled word path. -/
theorem fullDivN2PathConditionsWordV4_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  fullDivN2PathConditionsV4_overestimate bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hpath

/-- Project the selected carry package from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_selectedCarry
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.1

/-- Project the first selected n=2 carry component from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_carry_j2
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    let v := fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)
    let u := fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)
    if bltu_2 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word)
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.1 u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) :=
  fullDivN2SelectedCarryV4_j2 bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (fullDivN2SelectedPathConditionsWordV4_selectedCarry
      bltu_2 bltu_1 bltu_0 a b hpath)

/-- Project the second selected n=2 carry component from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_carry_j1
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    let v := fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)
    let u := fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)
    let r2 := fullDivN2R2V4 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    if bltu_1 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.1 r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1 :=
  fullDivN2SelectedCarryV4_j1 bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (fullDivN2SelectedPathConditionsWordV4_selectedCarry
      bltu_2 bltu_1 bltu_0 a b hpath)

/-- Project the third selected n=2 carry component from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_carry_j0
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    let v := fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)
    let u := fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)
    let r1 := fullDivN2R1V4 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    if bltu_0 then
      loopBodyN2CallAddbackCarry2NzV4 v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
    else
      isAddbackCarry2NzN2Max v.1 v.2.1 v.2.2.1 v.2.2.2
        u.1 r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1 :=
  fullDivN2SelectedCarryV4_j0 bltu_2 bltu_1 bltu_0
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (fullDivN2SelectedPathConditionsWordV4_selectedCarry
      bltu_2 bltu_1 bltu_0 a b hpath)

/-- Project the first v4 N2 trial-branch witness from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_trial_j2
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j2 bltu_2
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.1

/-- Project the second v4 N2 trial-branch witness from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_trial_j1
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j1 bltu_2 bltu_1
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.1

/-- Project the third v4 N2 trial-branch witness from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_trial_j0
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.1

/-- Project the v4 N2 normalized mulsub equation from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_mulsub
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.2.1

/-- Project the v4 N2 quotient-overestimate fact from the selected-carry word path. -/
theorem fullDivN2SelectedPathConditionsWordV4_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  hpath.2.2.2.2.2

/-- Semantic bridge for the n=2 v4 quotient word once callers provide the
    accumulated mulsub equation and quotient-overestimate bound. -/
theorem fullDivN2QuotientWordV4_eq_div_of_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool)
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3)
    (hge : fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
        a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let q0 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q1 := (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1
  let q2 := (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1
  let r0 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.1
  let r1 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
  let r2 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
  let r3 := (fullDivN2R0V4 bltu_2 bltu_1 bltu_0
    a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1
  have h_correct := div_correct_n2_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := q0) (q1 := q1) (q2 := q2)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3)
    hbnz (by simpa [fullDivN2MulSubEqV4, q0, q1, q2, r0, r1, r2, r3] using hmulsub)
    (by simpa [fullDivN2QuotientOverestimateV4, q0, q1, q2] using hge)
  delta fullDivN2QuotientWordV4
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

/-- Word-specialized n=2 v4 quotient bridge for callers that store the inputs as
    `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2QuotientWordV4_eq_div_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub : fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (hge : fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  have hraw :=
    fullDivN2QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
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

/-- Explicit-limb v4 quotient bridge from the bundled N2 path predicate. -/
theorem fullDivN2QuotientWordV4_eq_div_of_path_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN2PathConditionsV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b := by
  have hmulsub := fullDivN2PathConditionsV4_mulsub
    bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  have hge := fullDivN2PathConditionsV4_overestimate
    bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 hpath
  have hraw :=
    fullDivN2QuotientWordV4_eq_div_of_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  subst a0
  subst a1
  subst a2
  subst a3
  subst b0
  subst b1
  subst b2
  subst b3
  change
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
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

/-- EvmWord-level v4 quotient bridge from the bundled N2 path predicate. -/
theorem fullDivN2QuotientWordV4_eq_div_of_word_path_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN2QuotientWordV4_eq_div_of_path_conditions
    bltu_2 bltu_1 bltu_0 (a := a) (b := b)
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz hpath

/-- EvmWord-level v4 quotient bridge from the bundled N2 path predicate,
    accepting the public `b ≠ 0` nonzero form. -/
theorem fullDivN2QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN2QuotientWordV4_eq_div_of_word_path_conditions
    bltu_2 bltu_1 bltu_0 a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hpath

/-- EvmWord-level v4 quotient bridge from the selected-carry N2 path predicate.

    This avoids the false `fullDivN2Carry2NzV4`/`Carry2NzAll` package: quotient
    correctness only needs the selected path's mulsub equation and
    quotient-overestimate fact. -/
theorem fullDivN2QuotientWordV4_eq_div_of_selected_word_path_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN2QuotientWordV4_eq_div_of_getLimbN_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 hbnz
    (fullDivN2SelectedPathConditionsWordV4_mulsub bltu_2 bltu_1 bltu_0 a b hpath)
    (fullDivN2SelectedPathConditionsWordV4_overestimate bltu_2 bltu_1 bltu_0 a b hpath)

/-- EvmWord-level v4 quotient bridge from the selected-carry N2 path predicate,
    accepting the public `b ≠ 0` nonzero form. -/
theorem fullDivN2QuotientWordV4_eq_div_of_selected_word_path_conditions_ne_zero
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hpath : fullDivN2SelectedPathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b := by
  exact fullDivN2QuotientWordV4_eq_div_of_selected_word_path_conditions
    bltu_2 bltu_1 bltu_0 a b ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hpath

/-- If `fullDivN2QuotientWordV4 ... = EvmWord.div a b`, then each limb of
    `EvmWord.div a b` matches the corresponding v4 `fullDivN2R{0,1,2}` result
    and the top limb is zero. -/
theorem fullDivN2V4_hdivs_of_word_eq
    (bltu_2 bltu_1 bltu_0 : Bool)
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN2QuotientWordV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hdiv]
    delta fullDivN2QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_0
  · rw [← hdiv]
    delta fullDivN2QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_1
  · rw [← hdiv]
    delta fullDivN2QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN2QuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_3

/-- Explicit-limb v4 four-limb division witness from the bundled N2 path
    predicate. -/
theorem fullDivN2V4_getLimbN_of_path_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hpath : fullDivN2PathConditionsV4 bltu_2 bltu_1 bltu_0
      a0 a1 a2 a3 b0 b1 b2 b3) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V4 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V4 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V4 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hdivWord :=
    fullDivN2QuotientWordV4_eq_div_of_path_conditions
      bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hpath
  exact fullDivN2V4_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- EvmWord-level v4 four-limb division witness from the bundled N2 path
    predicate. -/
theorem fullDivN2V4_getLimbN_of_word_path_conditions
    (bltu_2 bltu_1 bltu_0 : Bool) (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hpath : fullDivN2PathConditionsWordV4 bltu_2 bltu_1 bltu_0 a b) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0V4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1V4 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2V4 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  exact fullDivN2V4_getLimbN_of_path_conditions
    bltu_2 bltu_1 bltu_0 (a := a) (b := b)
    (a0 := a.getLimbN 0) (a1 := a.getLimbN 1)
    (a2 := a.getLimbN 2) (a3 := a.getLimbN 3)
    (b0 := b.getLimbN 0) (b1 := b.getLimbN 1)
    (b2 := b.getLimbN 2) (b3 := b.getLimbN 3)
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz hpath

/-- n=2 quotient bridge specialized to the explicit limb variables used by the
    unified-bound wrappers. -/
theorem fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
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
    fullDivN2QuotientWord_eq_div_of_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  change
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
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

/-- n=2 quotient bridge specialized to branch constructors that store
    `a`/`b` as `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN2R2 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN2R2 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    fullDivN2QuotientWord bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b :=
  fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hge

/-- Explicit-limb n=2 four-limb division witness using the legacy
    quotient-overestimate hypothesis. -/
theorem fullDivN2_getLimbN_of_limbs_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      EvmWord.val256 a0 a1 a2 a3 =
        (((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1))
    (hge :
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        ((fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            a0 a1 a2 a3 b0 b1 b2 b3).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2 a0 a1 a2 a3 b0 b1 b2 b3).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  have hdivWord :=
    fullDivN2QuotientWord_eq_div_of_limbs_mulsub_overestimate
      bltu_2 bltu_1 bltu_0 ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
      hbnz hmulsub hge
  exact fullDivN2_hdivs_of_word_eq bltu_2 bltu_1 bltu_0
    a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord

/-- n=2 four-limb division witness specialized to branch constructors that
    store `a`/`b` as `EvmWord`s and refer to their limbs directly. -/
theorem fullDivN2_getLimbN_of_getLimbN_mulsub_overestimate
    (bltu_2 bltu_1 bltu_0 : Bool) {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hmulsub :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) =
        (((fullDivN2R2 bltu_2
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
              (a.getLimbN 0) (a.getLimbN 1)
              (a.getLimbN 2) (a.getLimbN 3)
              (b.getLimbN 0) (b.getLimbN 1)
              (b.getLimbN 2) (b.getLimbN 3)).1).toNat) *
          EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3) +
        EvmWord.val256
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1)
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1))
    (hge :
      EvmWord.val256 (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) /
        EvmWord.val256 (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3) ≤
        ((fullDivN2R2 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
          (b.getLimbN 3)).1).toNat * 2^128 +
          ((fullDivN2R1 bltu_2 bltu_1
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat * 2^64 +
          ((fullDivN2R0 bltu_2 bltu_1 bltu_0
            (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
            (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2)
            (b.getLimbN 3)).1).toNat) :
    (EvmWord.div a b).getLimbN 0 =
      (fullDivN2R0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 1 =
      (fullDivN2R1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 2 =
      (fullDivN2R2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
    (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  exact fullDivN2_getLimbN_of_limbs_mulsub_overestimate
    bltu_2 bltu_1 bltu_0 rfl rfl rfl rfl rfl rfl rfl rfl
    hbnz hmulsub hge

end EvmAsm.Evm64
