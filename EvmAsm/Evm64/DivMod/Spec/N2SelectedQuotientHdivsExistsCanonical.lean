/-
  EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivsExistsCanonical

  Canonical-bltu eliminator for `FullDivN2SelectedQuotientHdivs`: any package
  must have its `bltu2`, `bltu1`, and `bltu0` equal to the canonical values,
  so the derived hdiv facts hold at `n2V4CanonicalBltu{2,1,0}` directly.

  Downstream callers can use this to extract hdiv equations at the canonical
  bltu triple without going through an existential indirection.

  Mirrors `N3SelectedQuotientHdivsExistsCanonical` for the n=2 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2SelectedQuotientHdivs
public import EvmAsm.Evm64.DivMod.Spec.N2CallableSelectedShapeEvidenceCanonical

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The bltu values inside a `FullDivN2SelectedQuotientHdivs` package equal
    `n2V4CanonicalBltu{2,1,0}`. Stated as a non-existential variant of `.exists`
    that fixes the witnesses. -/
theorem FullDivN2SelectedQuotientHdivs.exists_canonical
    {a b : EvmWord}
    (hpkg : FullDivN2SelectedQuotientHdivs a b) :
    fullDivN2QuotientWordV4
        (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
        EvmWord.div a b ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN2R0V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b) (n2V4CanonicalBltu0 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN2R1V4 (n2V4CanonicalBltu2 a b) (n2V4CanonicalBltu1 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN2R2V4 (n2V4CanonicalBltu2 a b)
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  cases hpkg with
  | mk bltu2 bltu1 bltu0 hbltu2 hbltu1 hbltu0 hdivWord hdiv0 hdiv1 hdiv2 hdiv3 =>
      unfold isTrialN2V4_j2 at hbltu2
      unfold isTrialN2V4_j1 at hbltu1
      unfold isTrialN2V4_j0 at hbltu0
      subst hbltu2
      subst hbltu1
      subst hbltu0
      exact ⟨hdivWord, hdiv0, hdiv1, hdiv2, hdiv3⟩

end EvmAsm.Evm64
