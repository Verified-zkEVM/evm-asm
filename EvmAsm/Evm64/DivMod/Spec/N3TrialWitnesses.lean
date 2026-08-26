/-
  EvmAsm.Evm64.DivMod.Spec.N3TrialWitnesses

  Mechanical branch-boolean witnesses for the n=3 DIV path.

  Legacy note:
  Helpers below whose names end in `_of_path_conditions` still consume the old
  `fullDivN3Carry2NzV4` package. They are compatibility shims only. New v4
  stack/callable work should use the `_of_selected_path_conditions` helpers,
  which consume selected per-iteration carry evidence for the reachable path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN3LoopUnified
public import EvmAsm.Evm64.DivMod.Spec.N3QuotientStackBridge

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First-class proof bundle for the mechanical n=3 trial-branch witnesses at
    the public dispatcher surface.

    This carries only the branch booleans and their defining proof obligations;
    carry/addback and quotient correctness remain separate wrapper
    obligations. -/
inductive N3TrialWitnesses (a b : EvmWord) : Prop where
  | mk (bltu_1 bltu_0 : Bool)
      (hbltu_1 : isTrialN3_j1 bltu_1
        (a.getLimbN 3) (b.getLimbN 1) (b.getLimbN 2))
      (hbltu_0 : isTrialN3_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

/-- The two n=3 trial-branch booleans always have canonical witnesses.

    This packages the mechanical branch-enumeration part needed by
    unconditional n=3 stack wrappers. The remaining non-mechanical
    obligations are the carry/addback and semantic division witnesses. -/
theorem n3_trial_witnesses (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ∃ bltu_1 bltu_0,
      isTrialN3_j1 bltu_1 a3 b1 b2 ∧
      isTrialN3_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let shift := (clzResult b2).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let bltu_1 := BitVec.ult u4_s v2'
  let r1 := iterN3 bltu_1 v0' v1' v2' v3' u1S u2S u3S u4_s (0 : Word)
  let bltu_0 := BitVec.ult r1.2.2.2.1 v2'
  refine ⟨bltu_1, bltu_0, ?_, ?_⟩
  · simp [isTrialN3_j1, bltu_1, v2', u4_s, shift, antiShift]
  · simp [isTrialN3_j0, bltu_0, bltu_1, r1, v0', v1', v2', v3',
      u1S, u2S, u3S, u4_s, shift, antiShift]

/-- Bundled public-surface n=3 branch witnesses from the dispatcher shape
    hypotheses. -/
theorem n3TrialWitnesses_of_getLimbN_shape_shift_nz
    (a b : EvmWord)
    (_hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (_hb3z : b.getLimbN 3 = 0) (_hb2nz : b.getLimbN 2 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0) :
    N3TrialWitnesses a b := by
  obtain ⟨bltu_1, bltu_0, hbltu_1, hbltu_0⟩ :=
    n3_trial_witnesses
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  exact N3TrialWitnesses.mk bltu_1 bltu_0 hbltu_1 hbltu_0

/-- Eliminate an `N3TrialWitnesses` bundle into the explicit branch booleans
    and proof obligations expected by the existing stack-spec surfaces. -/
theorem N3TrialWitnesses.exists {a b : EvmWord}
    (h : N3TrialWitnesses a b) :
    ∃ bltu_1 bltu_0,
      isTrialN3_j1 bltu_1
        (a.getLimbN 3) (b.getLimbN 1) (b.getLimbN 2) ∧
      isTrialN3_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  cases h with
  | mk bltu_1 bltu_0 hbltu_1 hbltu_0 =>
      exact ⟨bltu_1, bltu_0, hbltu_1, hbltu_0⟩

/-- First-class proof bundle for the mechanical n=3 V4 trial-branch
    witnesses at the public dispatcher surface.

    This carries only the V4 branch booleans and their defining proof
    obligations; carry/addback and quotient correctness remain separate path
    obligations. -/
inductive N3V4TrialWitnesses (a b : EvmWord) : Prop where
  | mk (bltu_1 bltu_0 : Bool)
      (hbltu_1 : isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_0 : isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

/-- The two n=3 V4 trial-branch booleans always have canonical witnesses. -/
theorem n3_v4_trial_witnesses (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1 a0 a1 a2 a3 b0 b1 b2 b3 ∧
      isTrialN3V4_j0 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let bltu_1 :=
    BitVec.ult (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
      (fullDivN3NormV b0 b1 b2 b3).2.2.1
  let bltu_0 :=
    if bltu_1 then
      BitVec.ult
        (iterWithDoubleAddback
          (divKTrialCallV4QHat
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
            (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
            (fullDivN3NormV b0 b1 b2 b3).2.2.1)
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
    else
      BitVec.ult
        (iterN3Max
          (fullDivN3NormV b0 b1 b2 b3).1
          (fullDivN3NormV b0 b1 b2 b3).2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.1
          (fullDivN3NormV b0 b1 b2 b3).2.2.2
          (fullDivN3NormU a0 a1 a2 a3 b2).2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.1
          (fullDivN3NormU a0 a1 a2 a3 b2).2.2.2.2
          (0 : Word)).2.2.2.1
        (fullDivN3NormV b0 b1 b2 b3).2.2.1
  refine ⟨bltu_1, bltu_0, ?_, ?_⟩
  · unfold isTrialN3V4_j1
    rfl
  · unfold isTrialN3V4_j0
    rfl

/-- Bundled public-surface n=3 V4 branch witnesses. -/
theorem n3V4TrialWitnesses_of_getLimbN
    (a b : EvmWord) :
    N3V4TrialWitnesses a b := by
  obtain ⟨bltu_1, bltu_0, hbltu_1, hbltu_0⟩ :=
    n3_v4_trial_witnesses
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
  exact N3V4TrialWitnesses.mk bltu_1 bltu_0 hbltu_1 hbltu_0

/-- Eliminate an `N3V4TrialWitnesses` bundle into the explicit V4 branch
    booleans and proof obligations expected by path-condition wrappers. -/
theorem N3V4TrialWitnesses.exists {a b : EvmWord}
    (h : N3V4TrialWitnesses a b) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  cases h with
  | mk bltu_1 bltu_0 hbltu_1 hbltu_0 =>
      exact ⟨bltu_1, bltu_0, hbltu_1, hbltu_0⟩

/-- Legacy: assemble an existential bundled N3 V4 path predicate from the mechanical
    trial witness bundle plus the remaining carry/arithmetic obligations.

    The arithmetic continuation receives the concrete branch booleans and
    their defining equalities from `htrial`. This still consumes
    `fullDivN3Carry2NzV4`; prefer
    `N3V4TrialWitnesses.exists_selected_path_conditions` for new v4 work. -/
theorem N3V4TrialWitnesses.exists_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0, fullDivN3PathConditionsWordV4 bltu_1 bltu_0 a b := by
  cases htrial with
  | mk bltu_1' bltu_0' hbltu_1 hbltu_0 =>
      obtain ⟨hmulsub, hover⟩ := harith bltu_1' bltu_0' hbltu_1 hbltu_0
      exact ⟨bltu_1', bltu_0', hbltu_1, hbltu_0, hcarry2, hmulsub, hover⟩

/-- Assemble an existential selected-carry N3 V4 path predicate from the
    mechanical trial witness bundle plus selected carry/arithmetic obligations.

    Unlike `N3V4TrialWitnesses.exists_path_conditions`, this does not require
    or construct the false universal `fullDivN3Carry2NzV4` package. -/
theorem N3V4TrialWitnesses.exists_selected_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0, fullDivN3SelectedPathConditionsWordV4 bltu_1 bltu_0 a b := by
  cases htrial with
  | mk bltu_1' bltu_0' hbltu_1 hbltu_0 =>
      obtain ⟨hmulsub, hover⟩ := harith bltu_1' bltu_0' hbltu_1 hbltu_0
      exact ⟨bltu_1', bltu_0', hbltu_1, hbltu_0,
        hcarry bltu_1' bltu_0' hbltu_1 hbltu_0, hmulsub, hover⟩

/-- Legacy: assemble a V4 quotient-word equality from an `N3V4TrialWitnesses`
    bundle plus the remaining path-condition obligations.

    This still consumes `fullDivN3Carry2NzV4`; prefer the selected-path
    variant for new v4 stack/callable work. -/
theorem N3V4TrialWitnesses.exists_quotient_word_of_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_1, bltu_0, hpath⟩ :=
    N3V4TrialWitnesses.exists_path_conditions htrial hcarry2 harith
  exact ⟨bltu_1, bltu_0,
    fullDivN3PathConditionsWordV4_trial_j1 bltu_1 bltu_0 a b hpath,
    fullDivN3PathConditionsWordV4_trial_j0 bltu_1 bltu_0 a b hpath,
    fullDivN3QuotientWordV4_eq_div_of_word_path_conditions
      bltu_1 bltu_0 a b hbnz hpath⟩

/-- Assemble a V4 quotient-word equality from an `N3V4TrialWitnesses` bundle
    plus selected carry/path obligations, avoiding the false universal
    `fullDivN3Carry2NzV4` package. -/
theorem N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_1, bltu_0, hpath⟩ :=
    N3V4TrialWitnesses.exists_selected_path_conditions htrial hcarry harith
  exact ⟨bltu_1, bltu_0,
    fullDivN3SelectedPathConditionsWordV4_trial_j1 bltu_1 bltu_0 a b hpath,
    fullDivN3SelectedPathConditionsWordV4_trial_j0 bltu_1 bltu_0 a b hpath,
    fullDivN3QuotientWordV4_eq_div_of_selected_word_path_conditions
      bltu_1 bltu_0 a b hbnz hpath⟩

/-- Assemble concrete V4 quotient-limb witnesses from an `N3V4TrialWitnesses`
    bundle plus the remaining path-condition obligations. -/
theorem N3V4TrialWitnesses.exists_hdivs_of_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  obtain ⟨bltu_1, bltu_0, hbltu_1, hbltu_0, hdivWord⟩ :=
    N3V4TrialWitnesses.exists_quotient_word_of_path_conditions
      htrial hbnz hcarry2 harith
  exact ⟨bltu_1, bltu_0,
    hbltu_1, hbltu_0,
    fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Assemble concrete V4 quotient-limb witnesses from an `N3V4TrialWitnesses`
    bundle plus selected carry/path obligations, avoiding the false universal
    `fullDivN3Carry2NzV4` package. -/
theorem N3V4TrialWitnesses.exists_hdivs_of_selected_path_conditions
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  obtain ⟨bltu_1, bltu_0, hbltu_1, hbltu_0, hdivWord⟩ :=
    N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions
      htrial hbnz hcarry harith
  exact ⟨bltu_1, bltu_0,
    hbltu_1, hbltu_0,
    fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Nonzero-surface quotient-word witnesses from an `N3V4TrialWitnesses`
    bundle plus selected carry/path obligations. -/
theorem N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions_ne_zero
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  exact N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions
    htrial ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hcarry harith

/-- Nonzero-surface quotient-limb witnesses from an `N3V4TrialWitnesses`
    bundle plus selected carry/path obligations. -/
theorem N3V4TrialWitnesses.exists_hdivs_of_selected_path_conditions_ne_zero
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  exact N3V4TrialWitnesses.exists_hdivs_of_selected_path_conditions
    htrial ((EvmWord.ne_zero_iff_getLimbN_or).mp hbnz) hcarry harith

/-- Legacy nonzero-surface quotient-word witnesses from an
    `N3V4TrialWitnesses` bundle. This still consumes
    `fullDivN3Carry2NzV4`; prefer the selected-path quotient helpers for new
    v4 work. -/
theorem N3V4TrialWitnesses.exists_quotient_word_of_path_conditions_ne_zero
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_1, bltu_0, hpath⟩ :=
    N3V4TrialWitnesses.exists_path_conditions htrial hcarry2 harith
  exact ⟨bltu_1, bltu_0,
    fullDivN3PathConditionsWordV4_trial_j1 bltu_1 bltu_0 a b hpath,
    fullDivN3PathConditionsWordV4_trial_j0 bltu_1 bltu_0 a b hpath,
    fullDivN3QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
      bltu_1 bltu_0 a b hbnz hpath⟩

/-- Legacy nonzero-surface quotient-limb witnesses from an
    `N3V4TrialWitnesses` bundle. This still consumes
    `fullDivN3Carry2NzV4`; prefer the selected-path hdiv helpers for new v4
    work. -/
theorem N3V4TrialWitnesses.exists_hdivs_of_path_conditions_ne_zero
    {a b : EvmWord}
    (htrial : N3V4TrialWitnesses a b)
    (hbnz : b ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  by
    obtain ⟨bltu_1, bltu_0, hbltu_1, hbltu_0, hdivWord⟩ :=
      N3V4TrialWitnesses.exists_quotient_word_of_path_conditions_ne_zero
        htrial hbnz hcarry2 harith
    exact ⟨bltu_1, bltu_0, hbltu_1, hbltu_0,
      fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
        a b
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        hdivWord⟩

/-- Legacy auto-trial form of
    `N3V4TrialWitnesses.exists_quotient_word_of_path_conditions`.

    This constructs the mechanical V4 trial branch witnesses internally, so
    callers only provide the remaining carry and arithmetic path obligations.
    It still uses `fullDivN3Carry2NzV4`; prefer
    `n3V4_exists_quotient_word_of_selected_path_conditions`. -/
theorem n3V4_exists_quotient_word_of_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b :=
  N3V4TrialWitnesses.exists_quotient_word_of_path_conditions
    (n3V4TrialWitnesses_of_getLimbN a b) hbnz hcarry2 harith

/-- Auto-trial form of
    `N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions`.

    This constructs the mechanical V4 trial branch witnesses internally, so
    callers only provide the remaining selected carry and arithmetic path
    obligations. -/
theorem n3V4_exists_quotient_word_of_selected_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b :=
  N3V4TrialWitnesses.exists_quotient_word_of_selected_path_conditions
    (n3V4TrialWitnesses_of_getLimbN a b) hbnz hcarry harith

/-- Legacy slim auto-trial n=3 V4 quotient-word package.

    This keeps the selected branch booleans but drops their mechanical proof
    witnesses from the conclusion. It still consumes `fullDivN3Carry2NzV4`;
    prefer selected-path quotient helpers for new v4 work. -/
theorem n3V4_quotient_word_of_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_1, bltu_0, _, _, hdivWord⟩ :=
    n3V4_exists_quotient_word_of_path_conditions hbnz hcarry2 harith
  exact ⟨bltu_1, bltu_0, hdivWord⟩

/-- Legacy nonzero-surface n=3 V4 quotient-word package.

    This is the same witness package as `n3V4_quotient_word_of_path_conditions`,
    but accepts the stack-wrapper `b ≠ 0` premise directly. It still consumes
    `fullDivN3Carry2NzV4`; prefer selected-path quotient helpers for new v4
    work. -/
theorem n3V4_quotient_word_of_path_conditions_ne_zero
    {a b : EvmWord}
    (hbnz : b ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_1, bltu_0, hpath⟩ :=
    N3V4TrialWitnesses.exists_path_conditions
      (n3V4TrialWitnesses_of_getLimbN a b) hcarry2 harith
  exact ⟨bltu_1, bltu_0,
    fullDivN3QuotientWordV4_eq_div_of_word_path_conditions_ne_zero
      bltu_1 bltu_0 a b hbnz hpath⟩

/-- Legacy dispatcher-shape n=3 V4 quotient-word package.

    The shape hypotheses match the n=3 stack wrapper surface; the remaining
    non-mechanical obligations include the old `fullDivN3Carry2NzV4` package.
    Prefer selected-path quotient helpers for new v4 work. -/
theorem n3V4_shape_quotient_word_of_path_conditions
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (_hb3z : b.getLimbN 3 = 0) (_hb2nz : b.getLimbN 2 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b :=
  n3V4_quotient_word_of_path_conditions hbnz hcarry2 harith

/-- In the n=3 divisor shape, the nonzero second limb witnesses the full
    limb-or nonzero condition. -/
theorem n3_limb_or_ne_zero_of_limb2_ne_zero {b : EvmWord}
    (hb2nz : b.getLimbN 2 ≠ 0) :
    b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0 := by
  intro h_or
  exact hb2nz (EvmWord.or_eq_zero_imp_right (EvmWord.or_eq_zero_imp_left h_or))

/-- Legacy dispatcher-shape n=3 V4 quotient-word package deriving divisor
    nonzero from the n=3 shape itself. It still consumes
    `fullDivN3Carry2NzV4`; prefer selected-path quotient helpers for new v4
    work. -/
theorem n3V4_shape_quotient_word_of_path_conditions_of_hb2nz
    (a b : EvmWord)
    (_hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      fullDivN3QuotientWordV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b :=
  n3V4_shape_quotient_word_of_path_conditions
    a b (n3_limb_or_ne_zero_of_limb2_ne_zero hb2nz)
    _hb3z hb2nz _hshift_nz hcarry2 harith

/-- Legacy auto-trial form of
    `N3V4TrialWitnesses.exists_hdivs_of_path_conditions`.

    This is the pure witness package needed by n=3 unconditional wrappers once
    carry and arithmetic path obligations are available, but still consumes
    `fullDivN3Carry2NzV4`. Prefer the selected-path hdiv helper for new v4
    wrappers. -/
theorem n3V4_exists_hdivs_of_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  N3V4TrialWitnesses.exists_hdivs_of_path_conditions
    (n3V4TrialWitnesses_of_getLimbN a b) hbnz hcarry2 harith

/-- Auto-trial form of
    `N3V4TrialWitnesses.exists_hdivs_of_selected_path_conditions`.

    This constructs the mechanical V4 trial branch witnesses internally, so
    callers only provide the remaining selected carry and arithmetic path
    obligations. -/
theorem n3V4_exists_hdivs_of_selected_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry : ∀ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN3SelectedCarryV4 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      isTrialN3V4_j1 bltu_1
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN3V4_j0 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  N3V4TrialWitnesses.exists_hdivs_of_selected_path_conditions
    (n3V4TrialWitnesses_of_getLimbN a b) hbnz hcarry harith

/-- Legacy slim auto-trial n=3 V4 quotient-limb package.

    This is the consumer-facing form of
    `n3V4_exists_hdivs_of_path_conditions`: it keeps the selected branch
    booleans but drops their mechanical proof witnesses from the conclusion.
    It still consumes `fullDivN3Carry2NzV4`; prefer selected-path hdiv helpers
    for new v4 wrappers. -/
theorem n3V4_full_div_getLimbN_of_path_conditions
    {a b : EvmWord}
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) := by
  obtain ⟨bltu_1, bltu_0, hdivWord⟩ :=
    n3V4_quotient_word_of_path_conditions hbnz hcarry2 harith
  exact ⟨bltu_1, bltu_0,
    fullDivN3V4_hdivs_of_word_eq bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Nonzero-surface n=3 V4 quotient-limb package.

    This mirrors `n3V4_full_div_getLimbN_of_path_conditions` with the
    stack-wrapper `b ≠ 0` premise. -/
theorem n3V4_full_div_getLimbN_of_path_conditions_ne_zero
    {a b : EvmWord}
    (hbnz : b ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  by
    obtain ⟨bltu_1, bltu_0, _hbltu_1, _hbltu_0, hdivs⟩ :=
      N3V4TrialWitnesses.exists_hdivs_of_path_conditions_ne_zero
        (n3V4TrialWitnesses_of_getLimbN a b) hbnz hcarry2 harith
    exact ⟨bltu_1, bltu_0, hdivs⟩

/-- Dispatcher-shape n=3 V4 quotient-limb package.

    The shape hypotheses match the n=3 stack wrapper surface; the remaining
    non-mechanical obligations are the carry and arithmetic path facts. -/
theorem n3V4_shape_full_div_getLimbN_of_path_conditions
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (_hb3z : b.getLimbN 3 = 0) (_hb2nz : b.getLimbN 2 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  n3V4_full_div_getLimbN_of_path_conditions hbnz hcarry2 harith

/-- Dispatcher-shape n=3 V4 quotient-limb package deriving divisor nonzero
    from the n=3 shape itself. -/
theorem n3V4_shape_full_div_getLimbN_of_path_conditions_of_hb2nz
    (a b : EvmWord)
    (_hb3z : b.getLimbN 3 = 0) (hb2nz : b.getLimbN 2 ≠ 0)
    (_hshift_nz : (clzResult (b.getLimbN 2)).1 ≠ 0)
    (hcarry2 : fullDivN3Carry2NzV4
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
    (harith : ∀ bltu_1 bltu_0,
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
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN3R0V4 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN3R1V4 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 = (0 : Word) ∧
      (EvmWord.div a b).getLimbN 3 = (0 : Word) :=
  n3V4_shape_full_div_getLimbN_of_path_conditions
    a b (n3_limb_or_ne_zero_of_limb2_ne_zero hb2nz)
    _hb3z hb2nz _hshift_nz hcarry2 harith

end EvmAsm.Evm64
