/-
  EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

  Single-instance form for the universal callbacks inside
  `N3CallableSelectedShapeEvidence`. `isTrialN3V4_j{1,0}` are by definition
  `bltu_X = …`, so they uniquely determine the bltu pair from `(a, b)`.
  This file names that canonical pair and provides lifts from a pointed
  proof at the canonical pair to the universal callback form expected by
  `N3CallableSelectedShapeEvidence.of_parts`.

  Mirrors `N2CallableSelectedShapeEvidenceCanonical` for the n=3 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidence

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Canonical `bltu_1` value for the N3 v4 selected path at `(a, b)`. -/
def n3V4CanonicalBltu1 (a b : EvmWord) : Bool :=
  BitVec.ult
    (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
    (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).2.2.1

/-- Canonical `bltu_0` value for the N3 v4 selected path at `(a, b)`,
    constructed using the canonical `bltu_1`. -/
def n3V4CanonicalBltu0 (a b : EvmWord) : Bool :=
  if n3V4CanonicalBltu1 a b then
    BitVec.ult
      (iterWithDoubleAddback
        (divKTrialCallV4QHat
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
          (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
            (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
          (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
            (b.getLimbN 2) (b.getLimbN 3)).2.2.1)
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (0 : Word)).2.2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
  else
    BitVec.ult
      (iterN3Max
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.2
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.1
        (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
          (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
        (0 : Word)).2.2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1

/-- The canonical `bltu_1` satisfies the `isTrialN3V4_j1` predicate. -/
theorem isTrialN3V4_j1_n3V4CanonicalBltu1 (a b : EvmWord) :
    isTrialN3V4_j1 (n3V4CanonicalBltu1 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  unfold isTrialN3V4_j1 n3V4CanonicalBltu1
  rfl

/-- The canonical `bltu_0` satisfies the `isTrialN3V4_j0` predicate
    (with the canonical `bltu_1`). -/
theorem isTrialN3V4_j0_n3V4CanonicalBltu0 (a b : EvmWord) :
    isTrialN3V4_j0 (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  unfold isTrialN3V4_j0 n3V4CanonicalBltu0
  rfl

/-- Universal `selectedCarry` callback from a pointed proof at the canonical
    bltu pair. Any pair satisfying both trial-witness predicates equals the
    canonical pair, so the pointed proof suffices. -/
theorem n3CallableSelectedShapeEvidence_selectedCarry_of_canonical
    (a b : EvmWord)
    (h : fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  intro bltu_1 bltu_0 h1 h0
  unfold isTrialN3V4_j1 at h1
  unfold isTrialN3V4_j0 at h0
  subst h1
  subst h0
  exact h

/-- Universal `arithmetic` callback (mulsub ∧ overestimate) from a pointed
    proof at the canonical bltu pair. -/
theorem n3CallableSelectedShapeEvidence_arithmetic_of_canonical
    (a b : EvmWord)
    (h : fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3MulSubEqV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN3QuotientOverestimateV4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  intro bltu_1 bltu_0 h1 h0
  unfold isTrialN3V4_j1 at h1
  unfold isTrialN3V4_j0 at h0
  subst h1
  subst h0
  exact h

/-- Bundle the pointed canonical-bltu proofs into a full
    `N3CallableSelectedShapeEvidence`. -/
theorem N3CallableSelectedShapeEvidence.of_canonical {a b : EvmWord}
    (hcarry : fullDivN3SelectedCarryV4
      (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN3MulSubEqV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientOverestimateV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N3CallableSelectedShapeEvidence a b :=
  N3CallableSelectedShapeEvidence.of_parts
    (n3CallableSelectedShapeEvidence_selectedCarry_of_canonical a b hcarry)
    (n3CallableSelectedShapeEvidence_arithmetic_of_canonical a b harith)

end EvmAsm.Evm64
