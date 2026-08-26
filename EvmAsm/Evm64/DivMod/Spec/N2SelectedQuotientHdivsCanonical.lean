/-
  EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivsCanonical

  Convenience constructor for `FullDivN2SelectedQuotientHdivs` that takes
  pointed canonical-bltu evidence (selected carry plus mulsub ∧ overestimate
  at the canonical bltu triple) plus the n=2 divisor-shape facts, and routes
  through `N2CallableSelectedShapeEvidence.of_canonical` followed by
  `FullDivN2SelectedQuotientHdivs.of_shape_evidence`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivs
public import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Build the selected N2 quotient/hdiv package directly from pointed
    canonical-bltu evidence and the n=2 shape facts. -/
theorem FullDivN2SelectedQuotientHdivs.of_canonical
    {a b : EvmWord}
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1nz : b.getLimbN 1 ≠ 0)
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
    FullDivN2SelectedQuotientHdivs a b :=
  FullDivN2SelectedQuotientHdivs.of_shape_evidence hb3z hb2z hb1nz
    (N2CallableSelectedShapeEvidence.of_canonical hcarry harith)

end EvmAsm.Evm64
