/-
  EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonicalIff

  Equivalence between the universal-callback bundle
  `N2CallableSelectedShapeEvidence` and its pointed canonical-bltu form
  (selected carry and `mulsub ∧ overestimate` at `n2V4CanonicalBltu{2,1,0}`).

  - The reverse direction (canonical → bundle) is
    `N2CallableSelectedShapeEvidence.of_canonical`.
  - The forward direction (bundle → canonical) instantiates the universal
    callbacks at the canonical bltu triple, using the proven canonical
    trial-witness predicates.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Forward direction: specialize the universal callbacks in
    `N2CallableSelectedShapeEvidence` at the canonical bltu triple. -/
theorem N2CallableSelectedShapeEvidence.selectedCarry_canonical {a b : EvmWord}
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  N2CallableSelectedShapeEvidence.selectedCarry hevidence
    (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
    (isTrialN2V4_j2_n2V4CanonicalBltu2 a b)
    (isTrialN2V4_j1_n2V4CanonicalBltu1 a b)
    (isTrialN2V4_j0_n2V4CanonicalBltu0 a b)

/-- Forward direction: specialize the universal arithmetic callbacks at the
    canonical bltu triple. -/
theorem N2CallableSelectedShapeEvidence.arithmetic_canonical {a b : EvmWord}
    (hevidence : N2CallableSelectedShapeEvidence a b) :
    fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  N2CallableSelectedShapeEvidence.arithmetic hevidence
    (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
    (isTrialN2V4_j2_n2V4CanonicalBltu2 a b)
    (isTrialN2V4_j1_n2V4CanonicalBltu1 a b)
    (isTrialN2V4_j0_n2V4CanonicalBltu0 a b)

/-- The `N2CallableSelectedShapeEvidence` bundle is logically equivalent to
    the pair of pointed proofs (selected carry and `mulsub ∧ overestimate`)
    at the canonical bltu triple. -/
theorem N2CallableSelectedShapeEvidence_iff_canonical {a b : EvmWord} :
    N2CallableSelectedShapeEvidence a b ↔
      (fullDivN2SelectedCarryV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (fullDivN2MulSubEqV4
          (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4
          (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))) :=
  ⟨fun h =>
    ⟨N2CallableSelectedShapeEvidence.selectedCarry_canonical h,
     N2CallableSelectedShapeEvidence.arithmetic_canonical h⟩,
   fun ⟨hcarry, harith⟩ =>
    N2CallableSelectedShapeEvidence.of_canonical hcarry harith⟩

end EvmAsm.Evm64
