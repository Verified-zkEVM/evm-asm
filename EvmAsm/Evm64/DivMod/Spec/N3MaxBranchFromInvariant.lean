/-
  EvmAsm.Evm64.DivMod.Spec.N3MaxBranchFromInvariant

  Closes the N3 selected-carry MAX-branch predicates at the canonical bltu
  pair from a *named* set of inputs:

    1. shape hypothesis: `b3 = 0` and `b2 ≠ 0` (the n=3 shape predicate),
    2. shift normalisation facts (`v.2.2.2 = 0` and `2^63 ≤ v.2.2.1`),
    3. the canonical bltu_X = false condition,
    4. an instance of `MulsubMaxC3OneOfCarryZero` at the matching input.

  The bridge `isAddbackCarry2NzN3Max_of_not_ult_c3_one_of_carry_zero` from
  `DivN3MaxOverestimate` is invoked once per outer iteration j∈{1,0}.

  Inputs (2) and (4) are not derivable from shape alone (see
  `Counterexamples.ceN1MaxLocal_c3_one_of_carry_zero_false`); they are
  the structural normalisation facts and the per-iteration Knuth-B
  reachability invariant.  Naming them explicitly here turns the N3 MAX
  bead leaves into a composition with one named gap rather than free-form
  proof obligations.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivN3MaxOverestimate
public import EvmAsm.Evm64.DivMod.Spec.N3CallableSelectedShapeEvidenceCanonical

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- N3 j=1 MAX-branch carry-2-nz at the canonical bltu_1 = false, from
    structural normalisation facts and the named c3 invariant.

    `hv3z_norm` and `hv2_msb_norm` are the structural normalisation facts
    about `fullDivN3NormV`; closing them from `b3 = 0` + `b2 ≠ 0` + shift_nz
    is a separate work-list item (shift/clz lemma).

    `hc3` is the named `MulsubMaxC3OneOfCarryZero` instance at the matching
    `(v, u-window-at-j=1)` input.  Discharging it from selected-path
    reachability is the unified MAX-path frontier — see `DivMaxC3Invariant`. -/
theorem isAddbackCarry2NzN3Max_at_canonical_bltu1_false
    (a b : EvmWord)
    (hbltu1_false : n3V4CanonicalBltu1 a b = false)
    (hv3z_norm :
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2 = 0)
    (hv2_msb_norm :
      2^63 ≤ (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1.toNat)
    (hc3 : MulsubMaxC3OneOfCarryZero
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
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2) :
    isAddbackCarry2NzN3Max
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
      (0 : Word) := by
  -- The canonical bltu_1 unfolds to BitVec.ult of (NormU).2.2.2.2 against
  -- (NormV).2.2.1. The hypothesis hbltu1_false says that comparison is false.
  have hbltu : ¬ BitVec.ult
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).2.2.2.2
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := by
    unfold n3V4CanonicalBltu1 at hbltu1_false
    intro h
    rw [h] at hbltu1_false
    exact Bool.noConfusion hbltu1_false
  exact isAddbackCarry2NzN3Max_of_not_ult_c3_one_of_carry_zero _ _ _ _ _ _ _ _ _
    hv2_msb_norm hv3z_norm hc3 hbltu

/-- N3 j=0 MAX-branch carry-2-nz at the canonical bltu_0 = false, from
    structural normalisation facts and the named c3 invariant.

    Parametrised by `bltu_1 : Bool` since the j=0 input depends on the j=1
    iteration result `fullDivN3R1V4 bltu_1 a b`.  The `hbltu0_false`
    hypothesis is the unfolded MAX-branch form of `n3V4CanonicalBltu0`:
    comparing `(fullDivN3R1V4 bltu_1 …).2.2.1` (the post-j=1 third limb)
    against `v.2.2.1`. -/
theorem isAddbackCarry2NzN3Max_at_canonical_bltu0_false
    (a b : EvmWord) (bltu_1 : Bool)
    (hbltu0_false :
      BitVec.ult
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
          (b.getLimbN 2) (b.getLimbN 3)).2.2.1 = false)
    (hv3z_norm :
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2 = 0)
    (hv2_msb_norm :
      2^63 ≤ (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1.toNat)
    (hc3 : MulsubMaxC3OneOfCarryZero
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1) :
    isAddbackCarry2NzN3Max
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.2
      (fullDivN3NormU (a.getLimbN 0) (a.getLimbN 1)
        (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2)).1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 := by
  have hbltu : ¬ BitVec.ult
      (fullDivN3R1V4 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
      (fullDivN3NormV (b.getLimbN 0) (b.getLimbN 1)
        (b.getLimbN 2) (b.getLimbN 3)).2.2.1 := by
    intro h
    rw [h] at hbltu0_false
    exact Bool.noConfusion hbltu0_false
  exact isAddbackCarry2NzN3Max_of_not_ult_c3_one_of_carry_zero _ _ _ _ _ _ _ _ _
    hv2_msb_norm hv3z_norm hc3 hbltu

end EvmAsm.Evm64
