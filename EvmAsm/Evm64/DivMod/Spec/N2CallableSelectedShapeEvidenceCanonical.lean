/-
  EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

  Single-instance form for the universal callbacks inside
  `N2CallableSelectedShapeEvidence`. The trial-witness predicates
  `isTrialN2V4_j{2,1,0}` are by definition `bltu_X = BitVec.ult …`, so
  they uniquely determine the bltu triple from `(a, b)`. This file names
  that canonical triple and provides lifts from a pointed proof at the
  canonical instance to the universal callback form expected by
  `N2CallableSelectedShapeEvidence.of_parts`.

  Downstream proofs of the public N2 wrapper only have to discharge
  `fullDivN2SelectedCarryV4` and the `mulsub ∧ overestimate` conjunction
  at the canonical bltu triple, instead of universally quantifying over
  every triple that satisfies the trial predicates.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidence

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Canonical `bltu_2` value for the N2 v4 selected path at `(a, b)`. -/
def n2V4CanonicalBltu2 (a b : EvmWord) : Bool :=
  BitVec.ult
    (fullDivN2NormU (a.getLimbN 0) (a.getLimbN 1)
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 1)).2.2.2.2
    (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).2.1

/-- Canonical `bltu_1` value for the N2 v4 selected path at `(a, b)`. -/
def n2V4CanonicalBltu1 (a b : EvmWord) : Bool :=
  BitVec.ult
    (fullDivN2R2V4 (n2V4CanonicalBltu2 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
    (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).2.1

/-- Canonical `bltu_0` value for the N2 v4 selected path at `(a, b)`. -/
def n2V4CanonicalBltu0 (a b : EvmWord) : Bool :=
  BitVec.ult
    (fullDivN2R1V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
    (fullDivN2NormV (b.getLimbN 0) (b.getLimbN 1)
      (b.getLimbN 2) (b.getLimbN 3)).2.1

/-- The canonical `bltu_2` satisfies the `isTrialN2V4_j2` predicate. -/
theorem isTrialN2V4_j2_n2V4CanonicalBltu2 (a b : EvmWord) :
    isTrialN2V4_j2 (n2V4CanonicalBltu2 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  unfold isTrialN2V4_j2 n2V4CanonicalBltu2
  rfl

/-- The canonical `bltu_1` satisfies the `isTrialN2V4_j1` predicate
    (with the canonical `bltu_2`). -/
theorem isTrialN2V4_j1_n2V4CanonicalBltu1 (a b : EvmWord) :
    isTrialN2V4_j1 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  unfold isTrialN2V4_j1 n2V4CanonicalBltu1
  rfl

/-- The canonical `bltu_0` satisfies the `isTrialN2V4_j0` predicate
    (with the canonical `bltu_2` and `bltu_1`). -/
theorem isTrialN2V4_j0_n2V4CanonicalBltu0 (a b : EvmWord) :
    isTrialN2V4_j0 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
        (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  unfold isTrialN2V4_j0 n2V4CanonicalBltu0
  rfl

/-- Universal `selectedCarry` callback from a pointed proof at the canonical
    bltu triple. Any bltu triple satisfying all three trial-witness
    predicates equals the canonical triple, so the pointed proof suffices. -/
theorem n2CallableSelectedShapeEvidence_selectedCarry_of_canonical
    (a b : EvmWord)
    (h : fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2SelectedCarryV4 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  intro bltu_2 bltu_1 bltu_0 h2 h1 h0
  unfold isTrialN2V4_j2 at h2
  unfold isTrialN2V4_j1 at h1
  unfold isTrialN2V4_j0 at h0
  subst h2
  subst h1
  subst h0
  exact h

/-- Universal `arithmetic` callback (mulsub ∧ overestimate) from a pointed
    proof at the canonical bltu triple. -/
theorem n2CallableSelectedShapeEvidence_arithmetic_of_canonical
    (a b : EvmWord)
    (h : fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∀ bltu_2 bltu_1 bltu_0,
      isTrialN2V4_j2 bltu_2
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j1 bltu_2 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN2V4_j0 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN2MulSubEqV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN2QuotientOverestimateV4 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  intro bltu_2 bltu_1 bltu_0 h2 h1 h0
  unfold isTrialN2V4_j2 at h2
  unfold isTrialN2V4_j1 at h1
  unfold isTrialN2V4_j0 at h0
  subst h2
  subst h1
  subst h0
  exact h

/-- Bundle the pointed canonical-bltu proofs into a full
    `N2CallableSelectedShapeEvidence`. -/
theorem N2CallableSelectedShapeEvidence.of_canonical {a b : EvmWord}
    (hcarry : fullDivN2SelectedCarryV4
      (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : fullDivN2MulSubEqV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN2QuotientOverestimateV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    N2CallableSelectedShapeEvidence a b :=
  N2CallableSelectedShapeEvidence.of_parts
    (n2CallableSelectedShapeEvidence_selectedCarry_of_canonical a b hcarry)
    (n2CallableSelectedShapeEvidence_arithmetic_of_canonical a b harith)

end EvmAsm.Evm64
