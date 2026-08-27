/-
  EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivsExistsCanonical

  Canonical-bltu eliminator for `FullDivN3SelectedQuotientHdivs`: any package
  must have its `bltu1` and `bltu0` equal to the canonical values, so the
  derived hdiv facts hold at `n3V4CanonicalBltu{1,0}` directly.

  Downstream callers can use this to extract hdiv equations at the canonical
  bltu pair without going through an existential indirection.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivs
public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The bltu values inside a `FullDivN3SelectedQuotientHdivs` package equal
    `n3V4CanonicalBltu{1,0}`. Stated as a non-existential variant of `.exists`
    that fixes the witnesses. -/
theorem FullDivN3SelectedQuotientHdivs.exists_canonical
    {a b : EvmWord}
    (hpkg : FullDivN3SelectedQuotientHdivs a b) :
    fullDivN3QuotientWordV4
        (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 (n3V4CanonicalBltu1 a b) (n3V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 (n3V4CanonicalBltu1 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  cases hpkg with
  | mk bltu1 bltu0 hbltu1 hbltu0 hdivWord hdiv0 hdiv1 hdiv2 hdiv3 =>
      unfold isTrialN3V4_j1 at hbltu1
      unfold isTrialN3V4_j0 at hbltu0
      subst hbltu1
      subst hbltu0
      exact ⟨hdivWord, hdiv0, hdiv1, hdiv2, hdiv3⟩

end EvmAsm.Evm64
