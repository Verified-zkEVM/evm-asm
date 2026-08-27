/-
  EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonicalIff

  Equivalence between the universal-callback bundle
  `N3CallableSelectedShapeEvidence` and its pointed canonical-bltu form.
  Mirrors `N2CallableSelectedShapeEvidenceCanonicalIff` for the n=3 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Specialize the universal `selectedCarry` callback at the canonical
    bltu pair. -/
theorem N3CallableSelectedShapeEvidence.selectedCarry_canonical {a b : EvmWord}
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  N3CallableSelectedShapeEvidence.selectedCarry hevidence
    (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
    (isTrialN3V4_j1_n3V4CanonicalBltu1 a b)
    (isTrialN3V4_j0_n3V4CanonicalBltu0 a b)

/-- Specialize the universal arithmetic callback at the canonical bltu pair. -/
theorem N3CallableSelectedShapeEvidence.arithmetic_canonical {a b : EvmWord}
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) :=
  N3CallableSelectedShapeEvidence.arithmetic hevidence
    (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
    (isTrialN3V4_j1_n3V4CanonicalBltu1 a b)
    (isTrialN3V4_j0_n3V4CanonicalBltu0 a b)

/-- The `N3CallableSelectedShapeEvidence` bundle is logically equivalent to
    the pair of pointed proofs at the canonical bltu pair. -/
theorem N3CallableSelectedShapeEvidence_iff_canonical {a b : EvmWord} :
    N3CallableSelectedShapeEvidence a b ↔
      (fullDivN3SelectedCarryV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (fullDivN3MulSubEqV4
          (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN3QuotientOverestimateV4
          (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))) :=
  ⟨fun h =>
    ⟨N3CallableSelectedShapeEvidence.selectedCarry_canonical h,
     N3CallableSelectedShapeEvidence.arithmetic_canonical h⟩,
   fun ⟨hcarry, harith⟩ =>
    N3CallableSelectedShapeEvidence.of_canonical hcarry harith⟩

end EvmAsm.Evm64
