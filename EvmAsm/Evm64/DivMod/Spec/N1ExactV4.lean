/-
  EvmAsm.Evm64.DivMod.Spec.N1ExactV4

  Caller-facing full-v4 wrappers for exact N1 DIV stack specs.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1ExactNoNop
public import EvmAsm.Evm64.DivMod.Compose.FullPathN1V4PreloopCallMax
public import EvmAsm.Evm64.EvmWordArith.DivAccumulate

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmAsm.Rv64.AddrNorm (word_add_zero)

/-- The four quotient-limb equalities required by the N1 call/max/max/max
    stack postcondition. Naming this package gives the N1 hdiv bridge a
    single target instead of four repeated wrapper arguments. -/
abbrev FullDivN1CallMaxmaxmaxHdivs
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  (EvmWord.div a b).getLimbN 0 =
    (iterN1Max
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.1
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.2.1).1 ∧
  (EvmWord.div a b).getLimbN 1 =
    (loopN1CallMaxmaxmaxR1
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1).1 ∧
  (EvmWord.div a b).getLimbN 2 =
    (loopN1CallMaxmaxmaxR2
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      0 0 0
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).1 ∧
  (EvmWord.div a b).getLimbN 3 =
    (loopN1CallMaxmaxmaxR3
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      0 0 0).1

/-- Quotient word for the selected N1 v4 call/max/max/max path. This is
    intentionally separate from `fullDivN1QuotientWord true false false false`:
    the selected v4 j=3 call uses `divKTrialCallV4QHat`. -/
@[irreducible]
def fullDivN1CallMaxmaxmaxQuotientWordV4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : EvmWord :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := loopN1CallMaxmaxmaxR3
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
  let r2 := loopN1CallMaxmaxmaxR2
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1
  let r1 := loopN1CallMaxmaxmaxR1
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1 u.2.1
  let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with
    | 0 => r0.1
    | 1 => r1.1
    | 2 => r2.1
    | 3 => r3.1)

/-- Accumulated mulsub equation for the selected N1 v4 call/max/max/max
    quotient path. -/
abbrev FullDivN1CallMaxmaxmaxMulSubEqV4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := loopN1CallMaxmaxmaxR3
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
  let r2 := loopN1CallMaxmaxmaxR2
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1
  let r1 := loopN1CallMaxmaxmaxR1
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1 u.2.1
  let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  EvmWord.val256 a0 a1 a2 a3 =
    (r3.1.toNat * 2^192 + r2.1.toNat * 2^128 +
      r1.1.toNat * 2^64 + r0.1.toNat) *
      EvmWord.val256 b0 b1 b2 b3 +
    EvmWord.val256 r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1

/-- Quotient-overestimate bound for the selected N1 v4 call/max/max/max
    quotient path. -/
abbrev FullDivN1CallMaxmaxmaxQuotientOverestimateV4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := loopN1CallMaxmaxmaxR3
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
  let r2 := loopN1CallMaxmaxmaxR2
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1
  let r1 := loopN1CallMaxmaxmaxR1
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1 u.2.1
  let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
    r3.1.toNat * 2^192 + r2.1.toNat * 2^128 +
      r1.1.toNat * 2^64 + r0.1.toNat

/-- Semantic facts needed to bridge the selected N1 v4 call/max/max/max
    quotient word to `EvmWord.div`. -/
abbrev FullDivN1CallMaxmaxmaxSemanticFactsV4
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word) : Prop :=
  FullDivN1CallMaxmaxmaxMulSubEqV4 a0 a1 a2 a3 b0 b1 b2 b3 ∧
  FullDivN1CallMaxmaxmaxQuotientOverestimateV4 a0 a1 a2 a3 b0 b1 b2 b3

/-- Selected path evidence plus semantic facts for the canonical full-DIV N1
    v4 call/max/max/max route. This is the package later wrappers can target
    without exposing hdiv limbs or quotient-word equality. -/
abbrev FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word) :
    Prop :=
  fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal ∧
  FullDivN1CallMaxmaxmaxSemanticFactsV4 a0 a1 a2 a3 b0 b1 b2 b3

/-- Build the selected-path semantic evidence package from explicit selected
    branch/carry facts plus the semantic facts. -/
theorem FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_of_bltu_selected
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselected : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      a0 a1 a2 a3 b0 b1 b2 b3) :
    FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact ⟨
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_of_bltu_selected
      sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hselected,
    hfacts⟩

theorem FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_selectedInput
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal :=
  hevidence.1

theorem FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_semanticFacts
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    FullDivN1CallMaxmaxmaxSemanticFactsV4 a0 a1 a2 a3 b0 b1 b2 b3 :=
  hevidence.2

theorem FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_selectedCarry
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a0 a1 a2 a3 b0 b1 b2 b3
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1 := by
  exact fullDivN1CallMaxmaxmaxSelectedInputHypotheses_selectedCarry
    sp base
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a0 a1 a2 a3 b0 b1 b2 b3
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hevidence.1

theorem fullDivN1CallMaxmaxmaxHdivs_of_word_eq
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hdiv : fullDivN1CallMaxmaxmaxQuotientWordV4
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    FullDivN1CallMaxmaxmaxHdivs a b a0 a1 a2 a3 b0 b1 b2 b3 := by
  constructor
  · rw [← hdiv]
    delta fullDivN1CallMaxmaxmaxQuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_0
  constructor
  · rw [← hdiv]
    delta fullDivN1CallMaxmaxmaxQuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_1
  constructor
  · rw [← hdiv]
    delta fullDivN1CallMaxmaxmaxQuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_2
  · rw [← hdiv]
    delta fullDivN1CallMaxmaxmaxQuotientWordV4
    exact EvmWord.getLimbN_fromLimbs_3

/-- Semantic bridge for the selected N1 v4 call/max/max/max quotient word
    once the loop proof supplies the selected accumulated mulsub equation and
    quotient-overestimate bound. -/
theorem fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_mulsub_overestimate
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hmulsub :
      let v := fullDivN1NormV b0 b1 b2 b3
      let u := fullDivN1NormU a0 a1 a2 a3 b0
      let r3 := loopN1CallMaxmaxmaxR3
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
      let r2 := loopN1CallMaxmaxmaxR2
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
        u.2.2.1
      let r1 := loopN1CallMaxmaxmaxR1
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
        u.2.2.1 u.2.1
      let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      EvmWord.val256 a0 a1 a2 a3 =
        (r3.1.toNat * 2^192 + r2.1.toNat * 2^128 +
          r1.1.toNat * 2^64 + r0.1.toNat) *
          EvmWord.val256 b0 b1 b2 b3 +
        EvmWord.val256 r0.2.1 r0.2.2.1 r0.2.2.2.1 r0.2.2.2.2.1)
    (hge :
      let v := fullDivN1NormV b0 b1 b2 b3
      let u := fullDivN1NormU a0 a1 a2 a3 b0
      let r3 := loopN1CallMaxmaxmaxR3
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
      let r2 := loopN1CallMaxmaxmaxR2
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
        u.2.2.1
      let r1 := loopN1CallMaxmaxmaxR1
        v.1 v.2.1 v.2.2.1 v.2.2.2
        u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
        u.2.2.1 u.2.1
      let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
        r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
      EvmWord.val256 a0 a1 a2 a3 / EvmWord.val256 b0 b1 b2 b3 ≤
        r3.1.toNat * 2^192 + r2.1.toNat * 2^128 +
          r1.1.toNat * 2^64 + r0.1.toNat) :
    fullDivN1CallMaxmaxmaxQuotientWordV4 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  let v := fullDivN1NormV b0 b1 b2 b3
  let u := fullDivN1NormU a0 a1 a2 a3 b0
  let r3 := loopN1CallMaxmaxmaxR3
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
  let r2 := loopN1CallMaxmaxmaxR2
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1
  let r1 := loopN1CallMaxmaxmaxR1
    v.1 v.2.1 v.2.2.1 v.2.2.2
    u.2.2.2.1 u.2.2.2.2 (0 : Word) (0 : Word) (0 : Word)
    u.2.2.1 u.2.1
  let r0 := iterN1Max v.1 v.2.1 v.2.2.1 v.2.2.2 u.1
    r1.2.1 r1.2.2.1 r1.2.2.2.1 r1.2.2.2.2.1
  have h_correct := EvmWord.div_correct_n1_no_shift
    (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (b0 := b0) (b1 := b1) (b2 := b2) (b3 := b3)
    (q0 := r0.1) (q1 := r1.1) (q2 := r2.1) (q3 := r3.1)
    (r0 := r0.2.1) (r1 := r0.2.2.1)
    (r2 := r0.2.2.2.1) (r3 := r0.2.2.2.2.1)
    hbnz
    (by simpa [v, u, r3, r2, r1, r0] using hmulsub)
    (by simpa [v, u, r3, r2, r1, r0] using hge)
  delta fullDivN1CallMaxmaxmaxQuotientWordV4
  change
    EvmWord.fromLimbs (fun i : Fin 4 =>
      match i with
      | 0 => r0.1 | 1 => r1.1 | 2 => r2.1 | 3 => r3.1) =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3)
  exact h_correct.1

/-- Package-form semantic bridge for the selected N1 v4 call/max/max/max
    quotient word. -/
theorem fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_semantic_facts
    {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1CallMaxmaxmaxQuotientWordV4 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3)
        (EvmWord.fromLimbs fun i : Fin 4 =>
          match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) := by
  exact fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_mulsub_overestimate
    hbnz hfacts.1 hfacts.2

/-- Caller-word form of the package semantic bridge for the selected N1 v4
    call/max/max/max quotient word. -/
theorem fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_semantic_facts_word
    (a b : EvmWord) (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      a0 a1 a2 a3 b0 b1 b2 b3) :
    fullDivN1CallMaxmaxmaxQuotientWordV4 a0 a1 a2 a3 b0 b1 b2 b3 =
      EvmWord.div a b := by
  have hword := fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_semantic_facts
    hbnz hfacts
  have haWord :
      (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => a0 | 1 => a1 | 2 => a2 | 3 => a3) = a := by
    rw [← ha0, ← ha1, ← ha2, ← ha3]
    exact EvmWord.fromLimbs_match_getLimbN_id a
  have hbWord :
      (EvmWord.fromLimbs fun i : Fin 4 =>
        match i with | 0 => b0 | 1 => b1 | 2 => b2 | 3 => b3) = b := by
    rw [← hb0, ← hb1, ← hb2, ← hb3]
    exact EvmWord.fromLimbs_match_getLimbN_id b
  simpa [haWord, hbWord] using hword

/-- Direct full-v4 form of the N1 call/max/max/max exact-frame stack spec. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hcarry2 : Carry2NzAll
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (iterN1Max
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.2.1).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_stack_spec_within_word_v4_of_noNop base
    (evm_div_n1_call_maxmaxmax_stack_spec_within_word_noNop_v4_preNoX1_callableExtra_x9In_exactFrame_unified
      sp base a b
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
      nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
      raVal
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
      hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hcarry2
      hdiv0 hdiv1 hdiv2 hdiv3)

/-- Selected-carry full-v4 form of the N1 call/max/max/max exact-frame stack spec. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (iterN1Max
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.2.1).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  have hFull :=
    fullDivN1_preloop_call_maxmaxmax_denorm_epilogue_exact_x1_v4_x9In_of_selected
      sp base
      a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
      q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7 nMem shiftMem
      jMem retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hb3z hb2z hb1z hshift_nz halign hselected
  have hBody :
      cpsTripleWithin ((8 + 21 + 24 + 4 + 21 + 21 + 4 + 780) + (2 + 23 + 10))
        base (base + nopOff) (divCode_v4 base)
        (divModStackDispatchPreNoX1 sp a b x9In raVal
          ((clzResult b0).2 >>> (63 : Nat))
          v5 v6 v7 v10 v11Old
          q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
          shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
         ((sp + signExtend12 3936) ↦ₘ scratchMem))
        (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
         ((sp + signExtend12 3936) ↦ₘ
          divKTrialCallV4ScratchOut
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
            (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) :=
    cpsTripleWithin_weaken
      (fun h hp => by
        rw [divModStackDispatchPreNoX1_unfold] at hp
        rw [evmWordIs_sp_limbs_eq sp a _ _ _ _ ha0 ha1 ha2 ha3,
            evmWordIs_sp32_limbs_eq sp b _ _ _ _ hb0 hb1 hb2 hb3,
            divScratchValuesCallNoX1_unfold, divScratchValues_unfold] at hp
        rw [word_add_zero]
        xperm_hyp hp)
      (fun h hp => by
        have hConcrete :=
          fullDivN1CallMaxmaxmaxUnifiedPostNoX1_to_divConcretePostNoX1Frame_extra
            sp base (clzResult b0).1 a b
            a0 a1 a2 a3
            (fullDivN1NormV b0 b1 b2 b3).1
            (fullDivN1NormV b0 b1 b2 b3).2.1
            (fullDivN1NormV b0 b1 b2 b3).2.2.1
            (fullDivN1NormV b0 b1 b2 b3).2.2.2
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
            (0 : Word) (0 : Word) (0 : Word)
            (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
            (fullDivN1NormU a0 a1 a2 a3 b0).2.1
            (fullDivN1NormU a0 a1 a2 a3 b0).1
            scratchMem raVal
            ha0 ha1 ha2 ha3 hdiv0 hdiv1 hdiv2 hdiv3 h hp
        refine sepConj_mono_left (fun hLeft hpLeft => ?_) h hConcrete
        simpa [divStackDispatchPostCallableExactFrame_unfold] using
          divConcretePostNoX1_weaken_callable_frame sp a b hLeft hpLeft)
      hFull
  exact cpsTripleWithin_mono_nSteps (by unfold unifiedDivBound; decide) hBody

/-- Full-v4 N1 call/max/max/max exact-frame stack spec from branch facts plus
    selected carry facts, constructing the selected input package internally. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselectedCarry : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1)
    (hdiv0 : (EvmWord.div a b).getLimbN 0 =
      (iterN1Max
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.1
        (loopN1CallMaxmaxmaxR1
          (fullDivN1NormV b0 b1 b2 b3).1
          (fullDivN1NormV b0 b1 b2 b3).2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.1
          (fullDivN1NormV b0 b1 b2 b3).2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          0 0 0
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
          (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.2.2.2.1).1)
    (hdiv1 : (EvmWord.div a b).getLimbN 1 =
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).1)
    (hdiv2 : (EvmWord.div a b).getLimbN 2 =
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).1)
    (hdiv3 : (EvmWord.div a b).getLimbN 3 =
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).1) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  have hselected :=
    fullDivN1CallMaxmaxmaxSelectedInputHypotheses_of_bltu_selected sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hselectedCarry
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hselected
    hdiv0 hdiv1 hdiv2 hdiv3

/-- Selected-carry full-v4 N1 stack wrapper consuming the named hdiv package
    instead of four separate quotient-limb equalities. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_hdivs
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hdivs : FullDivN1CallMaxmaxmaxHdivs a b a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := hdivs
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hselected
    hdiv0 hdiv1 hdiv2 hdiv3

/-- Branch-and-selected-carry full-v4 N1 stack wrapper consuming the named
    hdiv package instead of four separate quotient-limb equalities. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry_hdivs
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselectedCarry : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1)
    (hdivs : FullDivN1CallMaxmaxmaxHdivs a b a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ := hdivs
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hselectedCarry
    hdiv0 hdiv1 hdiv2 hdiv3

/-- Selected-carry full-v4 N1 stack wrapper consuming selected quotient-word
    equality instead of an already-expanded hdiv package. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_word
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hdivWord : fullDivN1CallMaxmaxmaxQuotientWordV4
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_hdivs
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hselected
    (fullDivN1CallMaxmaxmaxHdivs_of_word_eq
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord)

/-- Selected-carry full-v4 N1 stack wrapper consuming the package of selected
    semantic facts instead of an already-expanded hdiv package. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_semantic_facts
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hselected : fullDivN1CallMaxmaxmaxSelectedInputHypotheses sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_word
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hselected
    (fullDivN1CallMaxmaxmaxQuotientWordV4_eq_div_of_semantic_facts_word
      a b a0 a1 a2 a3 b0 b1 b2 b3
      ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hfacts)

/-- Full-v4 N1 stack wrapper consuming a single selected-path semantic evidence
    package. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_semantic_evidence
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_semantic_facts
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hevidence.1 hevidence.2

/-- Branch-and-selected-carry full-v4 N1 stack wrapper consuming selected
    quotient-word equality instead of an already-expanded hdiv package. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry_word
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselectedCarry : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1)
    (hdivWord : fullDivN1CallMaxmaxmaxQuotientWordV4
      a0 a1 a2 a3 b0 b1 b2 b3 = EvmWord.div a b) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry_hdivs
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign hbltu3 hbltu2 hbltu1 hbltu0 hselectedCarry
    (fullDivN1CallMaxmaxmaxHdivs_of_word_eq
      a b a0 a1 a2 a3 b0 b1 b2 b3 hdivWord)

/-- Branch-and-selected-carry full-v4 N1 stack wrapper consuming the package of
    selected semantic facts instead of an already-expanded hdiv package. -/
theorem evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_carry_semantic_facts
    (sp base : Word) (a b : EvmWord)
    (a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In : Word)
    (q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
     nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem : Word)
    (raVal : Word)
    (ha0 : a.getLimbN 0 = a0) (ha1 : a.getLimbN 1 = a1)
    (ha2 : a.getLimbN 2 = a2) (ha3 : a.getLimbN 3 = a3)
    (hb0 : b.getLimbN 0 = b0) (hb1 : b.getLimbN 1 = b1)
    (hb2 : b.getLimbN 2 = b2) (hb3 : b.getLimbN 3 = b3)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0)
    (halign : fullDivN1CallMaxmaxmaxExactInputAligned sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal)
    (hbltu3 : isTrialN1_j3 true a3 b0)
    (hbltu2 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR3
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu1 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR2
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hbltu0 : ¬BitVec.ult
      (loopN1CallMaxmaxmaxR1
        (fullDivN1NormV b0 b1 b2 b3).1
        (fullDivN1NormV b0 b1 b2 b3).2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.1
        (fullDivN1NormV b0 b1 b2 b3).2.2.2
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
        0 0 0
        (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
        (fullDivN1NormU a0 a1 a2 a3 b0).2.1).2.1
      (fullDivN1NormV b0 b1 b2 b3).1)
    (hselectedCarry : loopN1CallMaxmaxmaxSelectedCarryFacts
      (fullDivN1NormV b0 b1 b2 b3).1
      (fullDivN1NormV b0 b1 b2 b3).2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.1
      (fullDivN1NormV b0 b1 b2 b3).2.2.2
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
      (0 : Word) (0 : Word) (0 : Word)
      (fullDivN1NormU a0 a1 a2 a3 b0).2.2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).2.1
      (fullDivN1NormU a0 a1 a2 a3 b0).1)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      a0 a1 a2 a3 b0 b1 b2 b3) :
    cpsTripleWithin unifiedDivBound base (base + nopOff) (divCode_v4 base)
      (divModStackDispatchPreNoX1 sp a b x9In raVal
        ((clzResult b0).2 >>> (63 : Nat))
        v5 v6 v7 v10 v11Old
        q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
        shiftMem nMem jMem retMem dMem dloMem scratchUn0 **
       ((sp + signExtend12 3936) ↦ₘ scratchMem))
      (divStackDispatchPostCallableExactFrame sp a b raVal (signExtend12 4095 : Word) **
       ((sp + signExtend12 3936) ↦ₘ
        divKTrialCallV4ScratchOut
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.2
          (fullDivN1NormU a0 a1 a2 a3 b0).2.2.2.1
          (fullDivN1NormV b0 b1 b2 b3).1 scratchMem)) := by
  exact evm_div_n1_call_maxmaxmax_stack_spec_within_word_v4_preNoX1_callableExtra_x9In_exactFrame_unified_of_selected_semantic_evidence
    sp base a b
    a0 a1 a2 a3 b0 b1 b2 b3 v5 v6 v7 v10 v11Old x9In
    q0 q1 q2 q3 u0Old u1Old u2Old u3Old u4Old u5 u6 u7
    nMem shiftMem jMem retMem dMem dloMem scratchUn0 scratchMem
    raVal
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3 hbnz hb3z hb2z hb1z
    hshift_nz halign
    (FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4_of_bltu_selected
      sp base
      jMem (1 : Word) (fullDivN1Shift b0) (fullDivN1NormU a0 a1 a2 a3 b0).1
      (a0 >>> ((fullDivN1AntiShift b0).toNat % 64)) v11Old (fullDivN1AntiShift b0)
      a0 a1 a2 a3 b0 b1 b2 b3
      (0 : Word) (0 : Word) (0 : Word) (0 : Word)
      retMem dMem dloMem scratchUn0 scratchMem raVal
      hbltu3 hbltu2 hbltu1 hbltu0 hselectedCarry hfacts)

end EvmAsm.Evm64
