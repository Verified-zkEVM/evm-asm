/-
  EvmAsm.Evm64.DivMod.Spec.N1TrialWitnesses

  Mechanical branch-boolean witnesses for the n=1 DIV path.
-/

module

public import EvmAsm.Evm64.DivMod.Compose.FullPathN1LoopUnified
public import EvmAsm.Evm64.DivMod.Spec.N1QuotientStackBridge
public import EvmAsm.Evm64.DivMod.Spec.N1Harith

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- First-class proof bundle for the mechanical n=1 trial-branch witnesses at the
    public dispatcher surface.

    The n=1 unconditional wrapper still needs the non-mechanical carry and
    quotient/remainder witnesses separately; this bundle packages only the
    branch booleans and their defining proof obligations. -/
inductive N1TrialWitnesses (a b : EvmWord) : Prop where
  | mk (bltu_3 bltu_2 bltu_1 bltu_0 : Bool)
      (hbltu_3 : isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0))
      (hbltu_2 : isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_1 : isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))
      (hbltu_0 : isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3))

/-- Selected n=1 raw path callback for mulsub equality plus quotient
    overestimate facts. -/
abbrev N1MulSubOverestimatePathCallback (a b : EvmWord) : Prop :=
  ∀ bltu_2 bltu_1 bltu_0,
    isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
    isTrialN1_j2 true bltu_2
      (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN1_j1 true bltu_2 bltu_1
      (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN1_j0 true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN1MulSubEq true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientOverestimate true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- Selected n=1 raw path callback for mulsub equality plus final-remainder
    facts. -/
abbrev N1MulSubRemainderLtPathCallback (a b : EvmWord) : Prop :=
  ∀ bltu_2 bltu_1 bltu_0,
    isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) →
    isTrialN1_j2 true bltu_2
      (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN1_j1 true bltu_2 bltu_1
      (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    isTrialN1_j0 true bltu_2 bltu_1 bltu_0
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
    fullDivN1MulSubEq true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1RemainderLt true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)

/-- The four n=1 trial-branch booleans always have canonical witnesses.

    This packages the mechanical branch-enumeration part needed by
    unconditional n=1 stack wrappers. The remaining non-mechanical
    obligations are the carry/addback and semantic division witnesses. -/
theorem n1_trial_witnesses (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 a3 b0 ∧
      isTrialN1_j2 bltu_3 bltu_2 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let bltu_3 := BitVec.ult u4_s v0'
  let r3 := iterN1 bltu_3 v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
  let bltu_2 := BitVec.ult r3.2.1 v0'
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2S r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let bltu_1 := BitVec.ult r2.2.1 v0'
  let r1 := iterN1 bltu_1 v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let bltu_0 := BitVec.ult r1.2.1 v0'
  refine ⟨bltu_3, bltu_2, bltu_1, bltu_0, ?_, ?_, ?_, ?_⟩
  · simp [isTrialN1_j3, bltu_3, v0', u4_s, shift, antiShift]
  · simp [isTrialN1_j2, bltu_2, bltu_3, r3, v0', v1', v2', v3', u3S, u4_s,
      shift, antiShift]
  · simp [isTrialN1_j1, bltu_1, bltu_2, bltu_3, r2, r3, v0', v1', v2', v3',
      u2S, u3S, u4_s, shift, antiShift]
  · simp [isTrialN1_j0, bltu_0, bltu_1, bltu_2, bltu_3, r1, r2, r3, v0', v1',
      v2', v3', u1S, u2S, u3S, u4_s, shift, antiShift]

/-- The first n=1 trial branch is forced true when the single divisor limb
    normalizes with a positive shift.

    This discharges the first branch certificate needed by unconditional n=1
    stack wrappers: the normalized top dividend fragment is below `2^63`,
    while the normalized divisor limb is at least `2^63`. -/
theorem isTrialN1_j3_true_of_shift_nz (a3 b0 : Word)
    (hb0nz : b0 ≠ 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    isTrialN1_j3 true a3 b0 := by
  unfold isTrialN1_j3
  have h_shift_pos : 1 ≤ (clzResult b0).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult b0).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h_u4_lt_pow63 :
      (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)).toNat <
        2^63 :=
    u_top_lt_pow63_of_shift_nz a3 (clzResult b0).1 h_shift_pos
      (clzResult_fst_toNat_le b0)
  have h_b0_ge_pow63 :
      (b0 <<< ((clzResult b0).1.toNat % 64)).toNat ≥ 2^63 :=
    b3_shifted_ge_pow63 hb0nz
  have h_lt :
      (a3 >>> ((signExtend12 (0 : BitVec 12) - (clzResult b0).1).toNat % 64)).toNat <
        (b0 <<< ((clzResult b0).1.toNat % 64)).toNat :=
    Nat.lt_of_lt_of_le h_u4_lt_pow63 h_b0_ge_pow63
  exact Eq.symm ((EvmWord.ult_iff).mpr h_lt)

/-- Branch-witness package for the n=1 call-first path.

    Under the n=1 nonzero/positive-shift conditions, the first trial branch is
    forced to `true`; the remaining branch booleans are chosen by their exact
    runtime comparisons. -/
theorem n1_trial_witnesses_call_first_of_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb0nz : b0 ≠ 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true a3 b0 ∧
      isTrialN1_j2 true bltu_2 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j1 true bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  let shift := (clzResult b0).1
  let antiShift := signExtend12 (0 : BitVec 12) - shift
  let v0' := b0 <<< (shift.toNat % 64)
  let v1' := (b1 <<< (shift.toNat % 64)) ||| (b0 >>> (antiShift.toNat % 64))
  let v2' := (b2 <<< (shift.toNat % 64)) ||| (b1 >>> (antiShift.toNat % 64))
  let v3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
  let u1S := (a1 <<< (shift.toNat % 64)) ||| (a0 >>> (antiShift.toNat % 64))
  let u2S := (a2 <<< (shift.toNat % 64)) ||| (a1 >>> (antiShift.toNat % 64))
  let u3S := (a3 <<< (shift.toNat % 64)) ||| (a2 >>> (antiShift.toNat % 64))
  let u4_s := a3 >>> (antiShift.toNat % 64)
  let r3 := iterN1 true v0' v1' v2' v3' u3S u4_s (0 : Word) (0 : Word) (0 : Word)
  let bltu_2 := BitVec.ult r3.2.1 v0'
  let r2 := iterN1 bltu_2 v0' v1' v2' v3' u2S r3.2.1 r3.2.2.1 r3.2.2.2.1 r3.2.2.2.2.1
  let bltu_1 := BitVec.ult r2.2.1 v0'
  let r1 := iterN1 bltu_1 v0' v1' v2' v3' u1S r2.2.1 r2.2.2.1 r2.2.2.2.1 r2.2.2.2.2.1
  let bltu_0 := BitVec.ult r1.2.1 v0'
  refine ⟨bltu_2, bltu_1, bltu_0, ?_, ?_, ?_, ?_⟩
  · exact isTrialN1_j3_true_of_shift_nz a3 b0 hb0nz hshift_nz
  · simp [isTrialN1_j2, bltu_2, r3, v0', v1', v2', v3', u3S, u4_s,
      shift, antiShift]
  · simp [isTrialN1_j1, bltu_1, bltu_2, r2, r3, v0', v1', v2', v3',
      u2S, u3S, u4_s, shift, antiShift]
  · simp [isTrialN1_j0, bltu_0, bltu_1, bltu_2, r1, r2, r3, v0', v1', v2',
      v3', u1S, u2S, u3S, u4_s, shift, antiShift]

/-- In the n=1 divisor-shape branch, nonzero divisor means the low limb is
    nonzero. -/
theorem b0_ne_zero_of_n1_shape (b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0) :
    b0 ≠ 0 := by
  intro hb0z
  apply hbnz
  simp [hb0z, hb1z, hb2z, hb3z]

/-- N=1 call-first branch witnesses directly from the dispatcher's n=1 shape
    hypotheses. -/
theorem n1_trial_witnesses_call_first_of_shape_shift_nz
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hbnz : b0 ||| b1 ||| b2 ||| b3 ≠ 0)
    (hb3z : b3 = 0) (hb2z : b2 = 0) (hb1z : b1 = 0)
    (hshift_nz : (clzResult b0).1 ≠ 0) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true a3 b0 ∧
      isTrialN1_j2 true bltu_2 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j1 true bltu_2 bltu_1 a1 a2 a3 b0 b1 b2 b3 ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0 a0 a1 a2 a3 b0 b1 b2 b3 := by
  exact n1_trial_witnesses_call_first_of_shift_nz
    a0 a1 a2 a3 b0 b1 b2 b3
    (b0_ne_zero_of_n1_shape b0 b1 b2 b3 hbnz hb3z hb2z hb1z)
    hshift_nz

/-- GetLimbN-level form of `n1_trial_witnesses_call_first_of_shape_shift_nz`,
    matching the public dispatcher branch surface. -/
theorem n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  exact n1_trial_witnesses_call_first_of_shape_shift_nz
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hbnz hb3z hb2z hb1z hshift_nz

/-- If a four-limb value is below one machine word, then its low limb is
    below that word. -/
theorem val256_limb0_lt_of_lt_word
    (x0 x1 x2 x3 bound : Word)
    (h_lt : EvmWord.val256 x0 x1 x2 x3 < bound.toNat) :
    x0.toNat < bound.toNat := by
  unfold EvmWord.val256 at h_lt
  omega

/-- A one-word bound on the first n=1 remainder forces the next trial branch
    to be the call branch. -/
theorem isTrialN1_j2_true_of_fullDivN1R3_remainder_lt
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R3 true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat) :
    isTrialN1_j2 true true a2 a3 b0 b1 b2 b3 := by
  unfold isTrialN1_j2
  unfold fullDivN1R3 fullDivN1NormV fullDivN1NormU
    fullDivN1Shift fullDivN1AntiShift at hr3_lt
  dsimp only at hr3_lt ⊢
  have h_ult := val256_limb0_lt_of_lt_word _ _ _ _
    (b0 <<< ((clzResult b0).1.toNat % 64)) hr3_lt
  unfold fullDivN1Shift at h_ult
  rw [show BitVec.ult
      (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
            (b1 <<< ((clzResult b0).1.toNat % 64) |||
              b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b2 <<< ((clzResult b0).1.toNat % 64) |||
              b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b3 <<< ((clzResult b0).1.toNat % 64) |||
              b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (a3 <<< ((clzResult b0).1.toNat % 64) |||
              a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            0 0 0).2.1
      (b0 <<< ((clzResult b0).1.toNat % 64)) = true by
    rw [EvmWord.ult_iff]
    exact h_ult]

/-- A one-word bound on the second n=1 remainder forces the next trial branch
    to be the call branch. -/
theorem isTrialN1_j1_true_of_fullDivN1R2_remainder_lt
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R2 true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat) :
    isTrialN1_j1 true true true a1 a2 a3 b0 b1 b2 b3 := by
  unfold isTrialN1_j1
  unfold fullDivN1R2 fullDivN1R3 fullDivN1NormV fullDivN1NormU
    fullDivN1Shift fullDivN1AntiShift at hr2_lt
  dsimp only at hr2_lt ⊢
  have h_ult := val256_limb0_lt_of_lt_word _ _ _ _
    (b0 <<< ((clzResult b0).1.toNat % 64)) hr2_lt
  unfold fullDivN1Shift at h_ult
  rw [show BitVec.ult
      (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
            (b1 <<< ((clzResult b0).1.toNat % 64) |||
              b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b2 <<< ((clzResult b0).1.toNat % 64) |||
              b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b3 <<< ((clzResult b0).1.toNat % 64) |||
              b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (a2 <<< ((clzResult b0).1.toNat % 64) |||
              a1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 <<< ((clzResult b0).1.toNat % 64) |||
                a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              0 0 0).2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 <<< ((clzResult b0).1.toNat % 64) |||
                a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              0 0 0).2.2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 <<< ((clzResult b0).1.toNat % 64) |||
                a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              0 0 0).2.2.2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 <<< ((clzResult b0).1.toNat % 64) |||
                a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              0 0 0).2.2.2.2.1).2.1
      (b0 <<< ((clzResult b0).1.toNat % 64)) = true by
    rw [EvmWord.ult_iff]
    exact h_ult]

/-- A one-word bound on the third n=1 remainder forces the final trial branch
    to be the call branch. -/
theorem isTrialN1_j0_true_of_fullDivN1R1_remainder_lt
    (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.1
        (fullDivN1R1 true true true a0 a1 a2 a3 b0 b1 b2 b3).2.2.2.2.1 <
      (fullDivN1NormV b0 b1 b2 b3).1.toNat) :
    isTrialN1_j0 true true true true a0 a1 a2 a3 b0 b1 b2 b3 := by
  unfold isTrialN1_j0
  unfold fullDivN1R1 fullDivN1R2 fullDivN1R3 fullDivN1NormV fullDivN1NormU
    fullDivN1Shift fullDivN1AntiShift at hr1_lt
  dsimp only at hr1_lt ⊢
  have h_ult := val256_limb0_lt_of_lt_word _ _ _ _
    (b0 <<< ((clzResult b0).1.toNat % 64)) hr1_lt
  unfold fullDivN1Shift at h_ult
  rw [show BitVec.ult
      (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
            (b1 <<< ((clzResult b0).1.toNat % 64) |||
              b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b2 <<< ((clzResult b0).1.toNat % 64) |||
              b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (b3 <<< ((clzResult b0).1.toNat % 64) |||
              b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (a1 <<< ((clzResult b0).1.toNat % 64) |||
              a0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a2 <<< ((clzResult b0).1.toNat % 64) |||
                a1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.2.1).2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a2 <<< ((clzResult b0).1.toNat % 64) |||
                a1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.2.1).2.2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a2 <<< ((clzResult b0).1.toNat % 64) |||
                a1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.2.1).2.2.2.1
            (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
              (b1 <<< ((clzResult b0).1.toNat % 64) |||
                b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b2 <<< ((clzResult b0).1.toNat % 64) |||
                b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (b3 <<< ((clzResult b0).1.toNat % 64) |||
                b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (a2 <<< ((clzResult b0).1.toNat % 64) |||
                a1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.1
              (iterN1 true (b0 <<< ((clzResult b0).1.toNat % 64))
                (b1 <<< ((clzResult b0).1.toNat % 64) |||
                  b0 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b2 <<< ((clzResult b0).1.toNat % 64) |||
                  b1 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (b3 <<< ((clzResult b0).1.toNat % 64) |||
                  b2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 <<< ((clzResult b0).1.toNat % 64) |||
                  a2 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                (a3 >>> ((signExtend12 0 - (clzResult b0).1).toNat % 64))
                0 0 0).2.2.2.2.1).2.2.2.2.1).2.1
      (b0 <<< ((clzResult b0).1.toNat % 64)) = true by
    rw [EvmWord.ult_iff]
    exact h_ult]

/-- The n=1 shape and the three one-word remainder bounds force all trial
    branches to take the call path. -/
theorem n1_trial_witnesses_all_true_of_remainders_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hr3_lt :
      EvmWord.val256
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr2_lt :
      EvmWord.val256
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R2 true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat)
    (hr1_lt :
      EvmWord.val256
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.1
        (fullDivN1R1 true true true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).2.2.2.2.1 <
      (fullDivN1NormV
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1.toNat) :
    isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
    isTrialN1_j2 true true
      (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    isTrialN1_j1 true true true
      (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
    isTrialN1_j0 true true true true
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact isTrialN1_j3_true_of_shift_nz
      (a.getLimbN 3) (b.getLimbN 0)
      (b0_ne_zero_of_n1_shape
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
        hbnz hb3z hb2z hb1z)
      hshift_nz
  · exact isTrialN1_j2_true_of_fullDivN1R3_remainder_lt
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hr3_lt
  · exact isTrialN1_j1_true_of_fullDivN1R2_remainder_lt
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hr2_lt
  · exact isTrialN1_j0_true_of_fullDivN1R1_remainder_lt
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hr1_lt

/-- Bundled public-surface n=1 branch witnesses from the dispatcher shape
    hypotheses, with the forced first branch recorded as `true`. -/
theorem n1TrialWitnesses_of_getLimbN_shape_shift_nz
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0) :
    N1TrialWitnesses a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0, hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  exact N1TrialWitnesses.mk true bltu_2 bltu_1 bltu_0
    hbltu_3 hbltu_2 hbltu_1 hbltu_0

/-- Eliminate an `N1TrialWitnesses` bundle into the explicit branch booleans
    and proof obligations expected by the existing stack-spec surfaces. -/
theorem N1TrialWitnesses.exists {a b : EvmWord}
    (h : N1TrialWitnesses a b) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  cases h with
  | mk bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0 =>
      exact ⟨bltu_3, bltu_2, bltu_1, bltu_0, hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩

/-- Eliminate an `N1TrialWitnesses` bundle and derive the quotient-word
    equality from compact raw path obligations supplied for the owned branch
    booleans. -/
theorem N1TrialWitnesses.exists_quotient_word
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  cases htrial with
  | mk bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0 =>
      obtain ⟨hmulsub, hge⟩ :=
        harith bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
      have hdivWord :=
        fullDivN1QuotientWord_eq_div_of_getLimbN_path_conditions
          bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
      exact ⟨bltu_3, bltu_2, bltu_1, bltu_0,
        hbltu_3, hbltu_2, hbltu_1, hbltu_0, hdivWord⟩

/-- Slim n=1 quotient-word package.

    This keeps the selected branch booleans but drops their mechanical proof
    witnesses from the conclusion. -/
theorem N1TrialWitnesses.quotient_word
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (harith : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0, _, _, _, _, hdivWord⟩ :=
    N1TrialWitnesses.exists_quotient_word htrial hbnz harith
  exact ⟨bltu_3, bltu_2, bltu_1, bltu_0, hdivWord⟩

/-- Shape-specialized n=1 quotient-word package.

    Under the n=1 divisor shape, the first trial branch is forced to `true`;
    this exposes only the remaining three selected branch booleans. -/
theorem n1_shape_quotient_word_of_mulsub_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_path_conditions
      true bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  exact ⟨bltu_2, bltu_1, bltu_0, hdivWord⟩

/-- Eliminate an `N1TrialWitnesses` bundle and derive all four quotient-limb
    witnesses from raw mulsub plus quotient-overestimate facts for the owned
    branch booleans. -/
theorem N1TrialWitnesses.exists_hdivs_of_mulsub_overestimate
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1QuotientOverestimate bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 bltu_3 bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 bltu_3 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  exact ⟨bltu_3, bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Eliminate an `N1TrialWitnesses` bundle and derive all four quotient-limb
    witnesses from raw mulsub plus final-remainder facts for the owned branch
    booleans. -/
theorem N1TrialWitnesses.exists_hdivs_of_mulsub_remainder_lt
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 bltu_3 bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 bltu_3 bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 bltu_3
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_3, bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    N1TrialWitnesses.exists htrial
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_remainder_lt
      bltu_3 bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt
  exact ⟨bltu_3, bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    fullDivN1_hdivs_of_word_eq bltu_3 bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Eliminate an `N1TrialWitnesses` bundle and derive the quotient-word
    equality from raw mulsub plus final-remainder obligations for the owned
    branch booleans. -/
theorem N1TrialWitnesses.exists_quotient_word_of_mulsub_remainder_lt
    {a b : EvmWord}
    (htrial : N1TrialWitnesses a b)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hpath : ∀ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) →
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) →
      fullDivN1MulSubEq bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
        fullDivN1RemainderLt bltu_3 bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)) :
    ∃ bltu_3 bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 bltu_3 (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 bltu_3 bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 bltu_3 bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      fullDivN1QuotientWord bltu_3 bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  exact N1TrialWitnesses.exists_quotient_word htrial hbnz
    (fun bltu_3 bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0 =>
      let hpair := hpath bltu_3 bltu_2 bltu_1 bltu_0
        hbltu_3 hbltu_2 hbltu_1 hbltu_0
      fullDivN1Harith_of_mulsub_remainder_lt
        bltu_3 bltu_2 bltu_1 bltu_0 hbnz hpair.1 hpair.2)

/-- Shape-specialized n=1 quotient-word package from raw mulsub plus
    final-remainder facts. -/
theorem n1_shape_quotient_word_of_mulsub_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubRemainderLtPathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      fullDivN1QuotientWord true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) =
          EvmWord.div a b := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_remainder_lt
      true bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt
  exact ⟨bltu_2, bltu_1, bltu_0, hdivWord⟩

/-- Shape-specialized n=1 hdiv witnesses from raw mulsub plus final-remainder
    facts, with the forced first branch recorded as `true`. -/
theorem n1_shape_hdivs_of_mulsub_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubRemainderLtPathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hmulsub, hrem_lt⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_remainder_lt
      true bltu_2 bltu_1 bltu_0 hbnz hmulsub hrem_lt
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Shape-specialized n=1 hdiv witnesses from raw mulsub plus
    quotient-overestimate facts, with the forced first branch recorded as
    `true`. -/
theorem n1_shape_hdivs_of_mulsub_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      isTrialN1_j3 true (a.getLimbN 3) (b.getLimbN 0) ∧
      isTrialN1_j2 true bltu_2
        (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j1 true bltu_2 bltu_1
        (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      isTrialN1_j0 true bltu_2 bltu_1 bltu_0
        (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
        (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ∧
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0,
      hbltu_3, hbltu_2, hbltu_1, hbltu_0⟩ :=
    n1_trial_witnesses_call_first_of_getLimbN_shape_shift_nz
      a b hbnz hb3z hb2z hb1z hshift_nz
  obtain ⟨hmulsub, hge⟩ :=
    hpath bltu_2 bltu_1 bltu_0 hbltu_3 hbltu_2 hbltu_1 hbltu_0
  have hdivWord :=
    fullDivN1QuotientWord_eq_div_of_getLimbN_mulsub_overestimate
      true bltu_2 bltu_1 bltu_0 hbnz hmulsub hge
  exact ⟨bltu_2, bltu_1, bltu_0,
    hbltu_3, hbltu_2, hbltu_1, hbltu_0,
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Acceptance-shaped n=1 full division limb theorem from raw mulsub plus
    quotient-overestimate facts. The remaining unconditional step is to
    discharge `hpath` from the n=1 schoolbook arithmetic. -/
theorem n1_full_div_getLimbN_of_mulsub_overestimate
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubOverestimatePathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0, hdivWord⟩ :=
    n1_shape_quotient_word_of_mulsub_overestimate
      a b hbnz hb3z hb2z hb1z hshift_nz hpath
  exact ⟨bltu_2, bltu_1, bltu_0,
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

/-- Acceptance-shaped n=1 full division limb theorem from raw mulsub plus
    final-remainder facts. The remaining unconditional step is to discharge
    `hpath` from the n=1 schoolbook arithmetic. -/
theorem n1_full_div_getLimbN_of_mulsub_remainder_lt
    (a b : EvmWord)
    (hbnz : b.getLimbN 0 ||| b.getLimbN 1 ||| b.getLimbN 2 |||
      b.getLimbN 3 ≠ 0)
    (hb3z : b.getLimbN 3 = 0) (hb2z : b.getLimbN 2 = 0)
    (hb1z : b.getLimbN 1 = 0)
    (hshift_nz : (clzResult (b.getLimbN 0)).1 ≠ 0)
    (hpath : N1MulSubRemainderLtPathCallback a b) :
    ∃ bltu_2 bltu_1 bltu_0,
      (EvmWord.div a b).getLimbN 0 =
        (fullDivN1R0 true bltu_2 bltu_1 bltu_0
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 1 =
        (fullDivN1R1 true bltu_2 bltu_1
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 2 =
        (fullDivN1R2 true bltu_2
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 ∧
      (EvmWord.div a b).getLimbN 3 =
        (fullDivN1R3 true
          (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
          (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)).1 := by
  obtain ⟨bltu_2, bltu_1, bltu_0, hdivWord⟩ :=
    n1_shape_quotient_word_of_mulsub_remainder_lt
      a b hbnz hb3z hb2z hb1z hshift_nz hpath
  exact ⟨bltu_2, bltu_1, bltu_0,
    fullDivN1_hdivs_of_word_eq true bltu_2 bltu_1 bltu_0
      a b
      (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
      (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
      hdivWord⟩

end EvmAsm.Evm64
