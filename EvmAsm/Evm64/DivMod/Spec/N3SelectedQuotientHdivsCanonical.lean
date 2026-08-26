/-
  EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivsCanonical

  Convenience constructor for `FullDivN3SelectedQuotientHdivs` that takes
  pointed canonical-bltu evidence (selected carry plus mulsub ∧ overestimate
  at the canonical bltu pair) plus the n=3 divisor-shape facts, and routes
  through `N3CallableSelectedShapeEvidence.of_canonical` followed by
  `FullDivN3SelectedQuotientHdivs.of_shape_evidence`.

  Mirrors `N2SelectedQuotientHdivsCanonical` for the n=3 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivs
public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Build the selected N3 quotient/hdiv package directly from pointed
    canonical-bltu evidence and the n=3 shape facts. -/
theorem FullDivN3SelectedQuotientHdivs.of_canonical
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
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
    FullDivN3SelectedQuotientHdivs a b :=
  FullDivN3SelectedQuotientHdivs.of_shape_evidence hb3z hb2nz
    (N3CallableSelectedShapeEvidence.of_canonical hcarry harith)

end EvmAsm.Evm64
