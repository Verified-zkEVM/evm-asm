/-
  EvmAsm.Evm64.DivMod.Spec.N3SelectedQuotientHdivs

  Private quotient-word and hdiv package for the selected N3 DIV v4 route.
  Mirrors `N2SelectedQuotientHdivs` for the n=3 lane.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidence

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- Selected N3 quotient package for the final public wrapper.

    The package names the branch witnesses, quotient-word equality, and four
    quotient-limb equalities produced from selected/reachable N3 evidence. -/
inductive FullDivN3SelectedQuotientHdivs (a b : EvmWord) : Prop where
  | mk (bltu1 bltu0 : Bool)
      (hbltu1 : isTrialN3V4_j1 bltu1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu0 : isTrialN3V4_j0 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hdivWord : fullDivN3QuotientWordV4 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b)
      (hdiv0 : (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu1 bltu0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
      (hdiv1 : (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1)
      (hdiv2 : (EvmWord.div a b).getLimbN 2 = (0 : Word))
      (hdiv3 : (EvmWord.div a b).getLimbN 3 = (0 : Word))

/-- Build the selected N3 quotient/hdiv package from the bundled selected
    evidence surface used by the final public route. -/
theorem FullDivN3SelectedQuotientHdivs.of_evidence
    {a b : EvmWord}
    (hbnz : b ≠ 0)
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    FullDivN3SelectedQuotientHdivs a b := by
  obtain ⟨bltu1, bltu0, hbltu1, hbltu0, hdivWord⟩ :=
    N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions_ne_zero
      (n3V4TrialWitnesses_of_getLimbN a b)
      hbnz
      (N3CallableSelectedShapeEvidence.selectedCarry hevidence)
      (N3CallableSelectedShapeEvidence.arithmetic hevidence)
  obtain ⟨hdiv0, hdiv1, hdiv2, hdiv3⟩ :=
    fullDivN3V4_hdivs_of_word_eq bltu1 bltu0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord
  exact ⟨bltu1, bltu0, hbltu1, hbltu0,
    hdivWord, hdiv0, hdiv1, hdiv2, hdiv3⟩

/-- Build the selected N3 quotient/hdiv package from the public n=3 divisor
    shape plus bundled selected evidence. -/
theorem FullDivN3SelectedQuotientHdivs.of_shape_evidence
    {a b : EvmWord}
    (_hb3z : b.getLimbN 3 = 0)
    (hb2nz : b.getLimbN 2 ≠ 0)
    (hevidence : N3CallableSelectedShapeEvidence a b) :
    FullDivN3SelectedQuotientHdivs a b := by
  exact FullDivN3SelectedQuotientHdivs.of_evidence
    ((EvmWord.ne_zero_iff_getLimbN_or).mpr
      (n3_limb_or_ne_zero_of_limb2_ne_zero hb2nz))
    hevidence

/-- Eliminate the selected N3 quotient/hdiv package into the explicit branch,
    quotient-word, and quotient-limb facts consumed by wrapper plumbing. -/
theorem FullDivN3SelectedQuotientHdivs.exists
    {a b : EvmWord}
    (hpkg : FullDivN3SelectedQuotientHdivs a b) :
    ∃ bltu1 bltu0,
      isTrialN3V4_j1 bltu1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu1 bltu0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu1 bltu0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  cases hpkg with
  | mk bltu1 bltu0 hbltu1 hbltu0 hdivWord hdiv0 hdiv1 hdiv2 hdiv3 =>
      exact ⟨bltu1, bltu0,
        hbltu1, hbltu0, hdivWord, hdiv0, hdiv1, hdiv2, hdiv3⟩

end EvmAsm.Evm64
