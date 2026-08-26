/-
  EvmAsm.Evm64.DivMod.Spec.N1CallableSelectedIfBorrowShapeEvidence

  Shared selected-if-borrow evidence bundle for the N1 DIV callable shape route.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N1ExactV4IfBorrowSelectedPath

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Private-style evidence bundle for the N1 selected-if-borrow callable shape
    route. This keeps branch facts, selected carry/path facts, and semantic
    arithmetic facts together while the final public wrapper is still being
    assembled. -/
abbrev N1CallableSelectedIfBorrowShapeEvidence (a b : EvmWord) : Prop :=
  isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR3
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR2
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  N1SelectedIfBorrowPathEvidence a b ∧
  FullDivN1CallMaxmaxmaxSemanticFactsV4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Branch facts carried by `N1CallableSelectedIfBorrowShapeEvidence`.
    Keeping this shape named lets later wrappers assemble the private evidence
    bundle without re-copying the long call/max/max/max branch predicate. -/
abbrev N1CallableSelectedIfBorrowBranchFacts (a b : EvmWord) : Prop :=
  isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR3
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR2
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1 ∧
  ¬BitVec.ult
    (loopN1CallMaxmaxmaxR1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.2.2
      0 0 0
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.2.1
      (fullDivN1NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 0)).2.1).2.1
    (fullDivN1NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).1

theorem N1CallableSelectedIfBorrowShapeEvidence.of_parts {a b : EvmWord}
    (hbranches : N1CallableSelectedIfBorrowBranchFacts a b)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  rcases hbranches with ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩
  exact ⟨hbltu3, hbltu2, hbltu1, hbltu0, hpath, hfacts⟩

/-- Build bundled callable evidence from explicit selected branch facts,
    all-true path evidence, and arithmetic semantic facts.

    This removes the selected semantic evidence package from the caller
    boundary; branch-fact discharge is left to the public wrapper layer. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.ofBranchFactsAllTruePathSemanticFacts
    {a b : EvmWord}
    (hbranches : N1CallableSelectedIfBorrowBranchFacts a b)
    (hpath : N1AllTruePathEvidence a b)
    (hfacts : FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  exact N1CallableSelectedIfBorrowShapeEvidence.of_parts hbranches
    (N1SelectedIfBorrowPathEvidence.ofAllTruePathEvidence hpath)
    hfacts


theorem N1CallableSelectedIfBorrowShapeEvidence.ofSelectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_branchFacts
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence
  exact ⟨hbltu3, hbltu2, hbltu1, hbltu0, hpath,
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_semanticFacts
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence⟩


/-- Project the selected branch facts from the bundled N1 callable evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.branchFacts {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    N1CallableSelectedIfBorrowBranchFacts a b := by
  rcases hevidence with ⟨hbltu3, hbltu2, hbltu1, hbltu0, _hpath, _hfacts⟩
  exact ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩

/-- Project selected reachable path evidence from the bundled N1 callable
    evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedPath {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    N1SelectedIfBorrowPathEvidence a b := by
  exact hevidence.2.2.2.2.1

/-- Project selected semantic facts from the bundled N1 callable evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.semanticFacts {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    FullDivN1CallMaxmaxmaxSemanticFactsV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact hevidence.2.2.2.2.2

/-- Rebuild the canonical selected-if-borrow semantic evidence package from
    the bundled N1 callable shape evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    N1CallableSelectedIfBorrowShapeEvidence.branchFacts hevidence
  exact FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_bltu_selected
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hbltu3 hbltu2 hbltu1 hbltu0
    (N1SelectedIfBorrowPathEvidence.selectedCarryIfBorrowFacts
      (N1CallableSelectedIfBorrowShapeEvidence.selectedPath hevidence))
    (N1CallableSelectedIfBorrowShapeEvidence.semanticFacts hevidence)

/-- Project the named selected-path hdiv package from the bundled N1
    callable shape evidence. This gives later N1 public-wrapper wiring a single
    private evidence object from which to recover the quotient-limb witnesses. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.hdivs
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact FullDivN1CallMaxmaxmaxHdivs_of_selected_if_borrow_semantic_evidence
    sp base a b
    jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    rfl rfl rfl rfl rfl rfl rfl rfl hbnz
    (N1CallableSelectedIfBorrowShapeEvidence.selectedIfBorrowSemanticEvidence
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence)

/-- Project the selected-if-borrow input hypotheses from the bundled N1
    callable shape evidence. This pairs with `hdivs` so downstream wrappers can
    consume one private evidence object at the selected path boundary. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedInput
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  exact FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_selectedInput
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    (N1CallableSelectedIfBorrowShapeEvidence.selectedIfBorrowSemanticEvidence
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence)

/-- Recover both selected-if-borrow stack inputs and hdiv witnesses from the
    bundled N1 callable shape evidence. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.selectedInputAndHdivs
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 ||| b.getLimbN 3 ≠ 0)
    (hevidence : N1CallableSelectedIfBorrowShapeEvidence a b) :
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal ∧
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact ⟨
    N1CallableSelectedIfBorrowShapeEvidence.selectedInput
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence,
    N1CallableSelectedIfBorrowShapeEvidence.hdivs
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hbnz hevidence⟩

/-- Word-equality variant of the selected-if-borrow N1 callable evidence.
    This is a narrower boundary than `N1CallableSelectedIfBorrowShapeEvidence`:
    callers carry the selected branch/path facts plus the quotient-word equality
    used by the stack postcondition, without exposing the raw semantic-facts
    conjunction. -/
abbrev N1CallableSelectedIfBorrowWordEvidence (a b : EvmWord) : Prop :=
  N1CallableSelectedIfBorrowBranchFacts a b ∧
  N1SelectedIfBorrowPathEvidence a b ∧
  fullDivN1CallMaxmaxmaxQuotientWordV4
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
      EvmWord.div a b

theorem N1CallableSelectedIfBorrowWordEvidence.of_parts {a b : EvmWord}
    (hbranches : N1CallableSelectedIfBorrowBranchFacts a b)
    (hpath : N1SelectedIfBorrowPathEvidence a b)
    (hword : fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b) :
    N1CallableSelectedIfBorrowWordEvidence a b :=
  ⟨hbranches, hpath, hword⟩

theorem N1CallableSelectedIfBorrowWordEvidence.branchFacts {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    N1CallableSelectedIfBorrowBranchFacts a b :=
  hevidence.1

theorem N1CallableSelectedIfBorrowWordEvidence.selectedPath {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    N1SelectedIfBorrowPathEvidence a b :=
  hevidence.2.1

theorem N1CallableSelectedIfBorrowWordEvidence.wordEq {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    fullDivN1CallMaxmaxmaxQuotientWordV4
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b :=
  hevidence.2.2

theorem N1CallableSelectedIfBorrowWordEvidence.selectedInput
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal := by
  obtain ⟨hbltu3, hbltu2, hbltu1, hbltu0⟩ :=
    N1CallableSelectedIfBorrowWordEvidence.branchFacts hevidence
  exact fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses_of_bltu_selected
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hbltu3 hbltu2 hbltu1 hbltu0
    (N1SelectedIfBorrowPathEvidence.selectedCarryIfBorrowFacts
      (N1CallableSelectedIfBorrowWordEvidence.selectedPath hevidence))

theorem N1CallableSelectedIfBorrowWordEvidence.hdivs {a b : EvmWord}
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact fullDivN1CallMaxmaxmaxHdivs_of_word_eq
    a b
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (N1CallableSelectedIfBorrowWordEvidence.wordEq hevidence)

theorem N1CallableSelectedIfBorrowWordEvidence.selectedInputAndHdivs
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hevidence : N1CallableSelectedIfBorrowWordEvidence a b) :
    fullDivN1CallMaxmaxmaxSelectedIfBorrowInputHypotheses sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal ∧
    FullDivN1CallMaxmaxmaxHdivs a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact ⟨
    N1CallableSelectedIfBorrowWordEvidence.selectedInput
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence,
    N1CallableSelectedIfBorrowWordEvidence.hdivs hevidence⟩

theorem N1CallableSelectedIfBorrowShapeEvidence.ofAllTruePathSelectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hpath : N1AllTruePathEvidence a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b :=
  N1CallableSelectedIfBorrowShapeEvidence.ofSelectedIfBorrowSemanticEvidence
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    (N1SelectedIfBorrowPathEvidence.ofAllTruePathEvidence hpath) hevidence

/-- Build the bundled callable evidence from the public n=1 shape plus the
    one-word remainder bounds that force the all-true path.

    This is an intermediate public-wrapper bridge: callers no longer need to
    expose the selected path package, while the selected-if-borrow semantic
    evidence still carries the call/max/max/max branch facts that cannot be
    derived from the all-true path alone. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.ofRemaindersLtSelectedIfBorrowSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hpath : N1AllTruePathCallback a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  exact N1CallableSelectedIfBorrowShapeEvidence.ofAllTruePathSelectedIfBorrowSemanticEvidence
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    (N1AllTruePathEvidence.ofRemaindersLt
      a b hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt hpath)
    hevidence

/-- Build the bundled callable evidence from the public n=1 shape, one-word
    remainder bounds, and the existing selected semantic evidence package.

    This keeps the selected-if-borrow package private to the bridge layer. -/
theorem N1CallableSelectedIfBorrowShapeEvidence.ofRemaindersLtSelectedSemanticEvidence
    (sp base : Word)
    (jOld v5Old v6Old v7Old v10Old v11Old v2Old : Word)
    (a b : EvmWord)
    (q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal : Word)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hpath : N1AllTruePathCallback a b)
    (hevidence : FullDivN1CallMaxmaxmaxSelectedSemanticEvidenceV4 sp base
      jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal) :
    N1CallableSelectedIfBorrowShapeEvidence a b := by
  exact N1CallableSelectedIfBorrowShapeEvidence.ofRemaindersLtSelectedIfBorrowSemanticEvidence
    sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
    a b q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
    hbnz hb3z hb2z hb1z hshift_nz hr3_lt hr2_lt hr1_lt hpath
    (FullDivN1CallMaxmaxmaxSelectedIfBorrowSemanticEvidenceV4_of_selected
      sp base jOld v5Old v6Old v7Old v10Old v11Old v2Old
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      q3Old q2Old q1Old q0Old retMem dMem dloMem scratchUn0 scratchMem raVal
      hevidence)


end EvmAsm.Evm64
