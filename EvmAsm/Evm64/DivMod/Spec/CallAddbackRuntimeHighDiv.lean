/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeHighDiv

  Small N4 call-addback runtime bridge lemmas that keep
  CallAddbackRuntime.lean below the file-size guardrail.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime

@[expose] public section

namespace EvmAsm.Evm64

namespace EvmWord

/-- High 128/64 quotient used by the n=4 call-addback Knuth-A bridge. -/
def n4CallAddbackBeqHighDivVal (a b : EvmWord) : Nat :=
  ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
      (n4CallAddbackBeqU3 a b).toNat) /
    (n4CallAddbackBeqB3Prime b).toNat

/-- The v4 call-addback qhat is no larger than the high 128/64 quotient. -/
def n4CallAddbackBeqQHatHighDivBound (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQHatV4 a b).toNat ≤
    n4CallAddbackBeqHighDivVal a b

/-- Knuth-A denominator bridge for the n=4 call-addback path.

    The v4 counterexample invalidated the stronger `≤ normDiv` target; this is
    the surviving `+1` shape used by the runtime-bounds bridge. -/
def n4CallAddbackBeqHighDivKnuthABound (a b : EvmWord) : Prop :=
  n4CallAddbackBeqHighDivVal a b ≤
    n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1

/-- The `rhatdd` high-half-zero fact used by the n=4 call-addback
    exact-floor bridge. -/
def n4CallAddbackBeqRhatddHiZero (a b : EvmWord) : Prop :=
  divKTrialCallV4Rhatdd
      (n4CallAddbackBeqU4 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
    (0 : Word)

/-- Packaged high-divisor evidence for the n=4, shift-nonzero call-addback
    runtime bridge.

    This is the compact dispatcher-facing evidence surface: exact-floor branch
    evidence (`rhatdd` high half zero), qhat bounded by the high 128/64
    quotient, and the surviving Knuth-A `+1` bridge from that quotient to the
    normalized 256-bit quotient. -/
def n4CallAddbackBeqShiftHighDivEvidence (a b : EvmWord) : Prop :=
  n4CallAddbackBeqRhatddHiZero a b ∧
    n4CallAddbackBeqQHatHighDivBound a b ∧
    n4CallAddbackBeqHighDivKnuthABound a b

/-- Compact qhat/high-divisor evidence for the n=4 call-addback runtime
    semantic bridge.

    Unlike `n4CallAddbackBeqShiftHighDivEvidence`, this package deliberately
    omits the exact-floor `rhatdd` fact. It is the addback-side evidence
    surface used after the direct qhat/high-div facts have already been
    established. -/
def n4CallAddbackBeqRuntimeQHatHighDivEvidence (a b : EvmWord) : Prop :=
  n4CallAddbackBeqQHatHighDivBound a b ∧
    n4CallAddbackBeqHighDivKnuthABound a b

theorem n4CallAddbackBeqHighDivVal_def {a b : EvmWord} :
    n4CallAddbackBeqHighDivVal a b =
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat :=
  rfl

theorem n4CallAddbackBeqQHatHighDivBound_def {a b : EvmWord} :
    n4CallAddbackBeqQHatHighDivBound a b =
      ((n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqHighDivVal a b) :=
  rfl

theorem n4CallAddbackBeqHighDivKnuthABound_def {a b : EvmWord} :
    n4CallAddbackBeqHighDivKnuthABound a b =
      (n4CallAddbackBeqHighDivVal a b ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :=
  rfl

theorem n4CallAddbackBeqRhatddHiZero_def {a b : EvmWord} :
    n4CallAddbackBeqRhatddHiZero a b =
      (divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :=
  rfl

theorem n4CallAddbackBeqShiftHighDivEvidence_def {a b : EvmWord} :
    n4CallAddbackBeqShiftHighDivEvidence a b =
      (n4CallAddbackBeqRhatddHiZero a b ∧
        n4CallAddbackBeqQHatHighDivBound a b ∧
        n4CallAddbackBeqHighDivKnuthABound a b) :=
  rfl

theorem n4CallAddbackBeqRuntimeQHatHighDivEvidence_def {a b : EvmWord} :
    n4CallAddbackBeqRuntimeQHatHighDivEvidence a b =
      (n4CallAddbackBeqQHatHighDivBound a b ∧
        n4CallAddbackBeqHighDivKnuthABound a b) :=
  rfl

theorem n4CallAddbackBeqShiftHighDivEvidence.of_parts {a b : EvmWord}
    (h_rhat_hi_zero : n4CallAddbackBeqRhatddHiZero a b)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b) :
    n4CallAddbackBeqShiftHighDivEvidence a b := by
  rw [n4CallAddbackBeqShiftHighDivEvidence_def]
  exact ⟨h_rhat_hi_zero, h_qhat_high, h_high_div⟩

theorem n4CallAddbackBeqShiftHighDivEvidence.rhatddHiZero {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqRhatddHiZero a b := by
  rw [n4CallAddbackBeqShiftHighDivEvidence_def] at h_evidence
  exact h_evidence.1

theorem n4CallAddbackBeqShiftHighDivEvidence.qhatHighDiv {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rw [n4CallAddbackBeqShiftHighDivEvidence_def] at h_evidence
  exact h_evidence.2.1

theorem n4CallAddbackBeqShiftHighDivEvidence.knuthA {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqHighDivKnuthABound a b := by
  rw [n4CallAddbackBeqShiftHighDivEvidence_def] at h_evidence
  exact h_evidence.2.2

theorem n4CallAddbackBeqRuntimeQHatHighDivEvidence.of_parts {a b : EvmWord}
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b) :
    n4CallAddbackBeqRuntimeQHatHighDivEvidence a b := by
  rw [n4CallAddbackBeqRuntimeQHatHighDivEvidence_def]
  exact ⟨h_qhat_high, h_high_div⟩

theorem n4CallAddbackBeqShiftHighDivEvidence.toRuntimeQHatHighDivEvidence
    {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b) :
    n4CallAddbackBeqRuntimeQHatHighDivEvidence a b :=
  n4CallAddbackBeqRuntimeQHatHighDivEvidence.of_parts
    (n4CallAddbackBeqShiftHighDivEvidence.qhatHighDiv h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.knuthA h_evidence)

theorem n4CallAddbackBeqRuntimeQHatHighDivEvidence.qhatHighDiv
    {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqRuntimeQHatHighDivEvidence a b) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rw [n4CallAddbackBeqRuntimeQHatHighDivEvidence_def] at h_evidence
  exact h_evidence.1

theorem n4CallAddbackBeqRuntimeQHatHighDivEvidence.knuthA
    {a b : EvmWord}
    (h_evidence : n4CallAddbackBeqRuntimeQHatHighDivEvidence a b) :
    n4CallAddbackBeqHighDivKnuthABound a b := by
  rw [n4CallAddbackBeqRuntimeQHatHighDivEvidence_def] at h_evidence
  exact h_evidence.2

theorem n4CallAddbackBeqQHatHighDivBound.of_le {a b : EvmWord}
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rwa [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def]

theorem n4CallAddbackBeqHighDivKnuthABound.of_le {a b : EvmWord}
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqHighDivKnuthABound a b := by
  rwa [n4CallAddbackBeqHighDivKnuthABound_def,
    n4CallAddbackBeqHighDivVal_def]

theorem n4CallAddbackBeqRuntimeQHatHighDivEvidence.of_raw_parts
    {a b : EvmWord}
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqRuntimeQHatHighDivEvidence a b :=
  n4CallAddbackBeqRuntimeQHatHighDivEvidence.of_parts
    (n4CallAddbackBeqQHatHighDivBound.of_le h_qhat_le_high_div)
    (n4CallAddbackBeqHighDivKnuthABound.of_le h_high_div_le_norm_plus_one)

theorem n4CallAddbackBeqRhatddHiZero.of_eq {a b : EvmWord}
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :
    n4CallAddbackBeqRhatddHiZero a b := by
  rwa [n4CallAddbackBeqRhatddHiZero_def]

theorem n4CallAddbackBeqShiftHighDivEvidence.of_raw_parts {a b : EvmWord}
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqShiftHighDivEvidence a b :=
  n4CallAddbackBeqShiftHighDivEvidence.of_parts
    (n4CallAddbackBeqRhatddHiZero.of_eq h_rhat_hi_zero)
    (n4CallAddbackBeqQHatHighDivBound.of_le h_qhat_le_high_div)
    (n4CallAddbackBeqHighDivKnuthABound.of_le h_high_div_le_norm_plus_one)

theorem n4CallAddbackBeqQHatHighDivBound.of_floor_eq {a b : EvmWord}
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat) :
    n4CallAddbackBeqQHatHighDivBound a b := by
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def]
  omega

theorem n4CallAddbackBeqShiftHighDivEvidence.of_floor_parts {a b : EvmWord}
    (h_rhat_hi_zero : n4CallAddbackBeqRhatddHiZero a b)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b) :
    n4CallAddbackBeqShiftHighDivEvidence a b :=
  n4CallAddbackBeqShiftHighDivEvidence.of_parts
    h_rhat_hi_zero
    (n4CallAddbackBeqQHatHighDivBound.of_floor_eq h_floor)
    h_high_div

theorem n4CallAddbackBeqShiftHighDivEvidence.of_floor_raw_parts {a b : EvmWord}
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1) :
    n4CallAddbackBeqShiftHighDivEvidence a b :=
  n4CallAddbackBeqShiftHighDivEvidence.of_floor_parts
    (n4CallAddbackBeqRhatddHiZero.of_eq h_rhat_hi_zero)
    h_floor
    (n4CallAddbackBeqHighDivKnuthABound.of_le h_high_div_le_norm_plus_one)

theorem n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b) :
    (n4CallAddbackBeqQHatV4 a b).toNat = n4CallAddbackBeqHighDivVal a b := by
  rw [n4CallAddbackBeqHighDivVal_def]
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def] at h_qhat_high
  exact n4CallAddbackBeqQHatV4_eq_floor_of_call_rhatdd_hi_zero_of_le
    hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high

/-- Runtime-bounds package from the named high-divisor qhat and Knuth-A
    bridge predicates. -/
theorem n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [n4CallAddbackBeqQHatHighDivBound_def,
    n4CallAddbackBeqHighDivVal_def] at h_qhat_high
  rw [n4CallAddbackBeqHighDivKnuthABound_def,
    n4CallAddbackBeqHighDivVal_def] at h_high_div
  exact n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    hb3nz (le_trans h_qhat_high h_high_div) h_borrow

/-- Runtime semantic bridge from the named high-divisor qhat and Knuth-A
    bridge predicates. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
      hb3nz h_qhat_high h_high_div h_borrow)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_high_div_bounds_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
      hb3nz hshift_nz h_qhat_high h_high_div h_borrow h_carry2

/-- Runtime-bounds package from exact-floor qhat evidence and the named
    Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqRuntimeBounds_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatHighDivBound.of_floor_eq h_floor)
    h_high_div
    h_borrow

/-- Runtime semantic bridge from exact-floor qhat evidence and the named
    Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_high_div_bounds_and_borrow
    hb3nz hshift_nz
    (n4CallAddbackBeqQHatHighDivBound.of_floor_eq h_floor)
    h_high_div
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_floor_eq_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
      hb3nz hshift_nz h_floor h_high_div h_borrow h_carry2

/-- Runtime-bounds package from the call-path exact-floor bridge and the
    named Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqRuntimeBounds_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_floor_eq_high_div_bound_and_borrow
    hb3nz
    (by
      simpa [n4CallAddbackBeqHighDivVal_def] using
        n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
          hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high)
    h_high_div h_borrow

/-- Runtime semantic bridge from the call-path exact-floor bridge and the
    named Knuth-A high-divisor bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_high_div_bound_and_borrow
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqHighDivVal_def] using
        n4CallAddbackBeqQHatHighDivBound.floor_eq_of_call_rhatdd_hi_zero
          hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high)
    h_high_div h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_call_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- EVM-word spelling of
    `n4CallAddbackBeqRuntimeBounds_of_call_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqRuntimeBounds_of_call_evm_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b := by
  rw [isCallTrialN4Evm_def] at hcall
  exact n4CallAddbackBeqRuntimeBounds_of_call_high_div_bound_and_borrow
    hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high h_high_div h_borrow

/-- EVM-word spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  rw [isCallTrialN4Evm_def] at hcall
  exact n4CallAddbackBeqSemanticHoldsV4_of_call_high_div_bound_and_borrow
    hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_call_evm_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- Shift-nonzero spelling of
    `n4CallAddbackBeqRuntimeBounds_of_call_evm_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqRuntimeBounds_of_shift_nz_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_call_evm_high_div_bound_and_borrow
    hb3nz hshift_nz
    (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    h_rhat_hi_zero h_qhat_high h_high_div h_borrow

/-- Shift-nonzero spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_nz_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow
    hb3nz hshift_nz
    (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_nz_high_div_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_nz_high_div_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_high : n4CallAddbackBeqQHatHighDivBound a b)
    (h_high_div : n4CallAddbackBeqHighDivKnuthABound a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_nz_high_div_bound_and_borrow
      hb3nz hshift_nz h_rhat_hi_zero h_qhat_high h_high_div h_borrow h_carry2

/-- Call-path semantic bridge from packaged high-div evidence.
    This is the call-local runtime wrapper shape needed by the final
    runtime-only discharger: the old `hq_over` and `h_rem_lt` obligations are
    hidden behind the named high-div evidence package. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_call_evm_high_div_bound_and_borrow
    hb3nz hshift_nz hcall
    (by
      simpa [n4CallAddbackBeqRhatddHiZero_def] using
        n4CallAddbackBeqShiftHighDivEvidence.rhatddHiZero h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.qhatHighDiv h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.knuthA h_evidence)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_evidence`. -/
theorem n4CallAddbackBeqSemanticHolds_of_call_runtime_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_evidence
      hb3nz hshift_nz hcall h_evidence h_borrow h_carry2

/-- Shift-nonzero semantic bridge from packaged high-div evidence. It derives
    the call-trial premise internally from the n=4 top-limb and shift facts,
    while still keeping the named high-div evidence explicit. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_evidence
    hb3nz hshift_nz (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    h_evidence h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_evidence`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_runtime_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_evidence
      hb3nz hshift_nz h_evidence h_borrow h_carry2

/-- Call-path semantic bridge from raw high-div evidence parts. This names the
    route from concrete arithmetic facts into the packaged runtime semantic
    bridge, keeping the final runtime-only path off the compact `RuntimeBounds`
    predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_evidence
    hb3nz hshift_nz hcall
    (n4CallAddbackBeqShiftHighDivEvidence.of_raw_parts
      h_rhat_hi_zero h_qhat_le_high_div h_high_div_le_norm_plus_one)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_raw_parts`. -/
theorem n4CallAddbackBeqSemanticHolds_of_call_runtime_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4Evm a b)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_raw_parts
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Shift-nonzero semantic bridge from raw high-div evidence parts, deriving
    the call-trial premise internally. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_call_runtime_high_div_raw_parts
    hb3nz hshift_nz (isCallTrialN4Evm_of_shift_nz a b hb3nz hshift_nz)
    h_rhat_hi_zero h_qhat_le_high_div h_high_div_le_norm_plus_one
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_raw_parts`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_runtime_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_raw_parts
      hb3nz hshift_nz h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Runtime-bounds bridge from packaged shift/high-div evidence. -/
theorem n4CallAddbackBeqRuntimeBounds_of_shift_high_div_evidence_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_shift_nz_high_div_bound_and_borrow
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqRhatddHiZero_def] using
        n4CallAddbackBeqShiftHighDivEvidence.rhatddHiZero h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.qhatHighDiv h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.knuthA h_evidence)
    h_borrow

/-- Runtime semantic bridge from packaged shift/high-div evidence. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_evidence_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_shift_nz_high_div_bound_and_borrow
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqRhatddHiZero_def] using
        n4CallAddbackBeqShiftHighDivEvidence.rhatddHiZero h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.qhatHighDiv h_evidence)
    (n4CallAddbackBeqShiftHighDivEvidence.knuthA h_evidence)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_evidence_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_high_div_evidence_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_evidence_and_borrow
      hb3nz hshift_nz h_evidence h_borrow h_carry2

/-- Runtime-bounds bridge from raw shift/high-div evidence. -/
theorem n4CallAddbackBeqRuntimeBounds_of_shift_high_div_raw_parts_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_shift_high_div_evidence_and_borrow
    hb3nz hshift_nz
    (n4CallAddbackBeqShiftHighDivEvidence.of_raw_parts
      h_rhat_hi_zero h_qhat_le_high_div h_high_div_le_norm_plus_one)
    h_borrow

/-- Runtime semantic bridge from raw shift/high-div evidence. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_raw_parts_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_shift_runtime_high_div_raw_parts
    hb3nz hshift_nz h_rhat_hi_zero h_qhat_le_high_div
    h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_raw_parts_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_high_div_raw_parts_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_raw_parts_and_borrow
      hb3nz hshift_nz h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Runtime-bounds package from a direct qhat high-divisor bound, the weakened
    Knuth-A `+1` denominator bridge, and the runtime borrow predicate. -/
theorem n4CallAddbackBeqRuntimeBounds_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_high_div_bounds_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatHighDivBound.of_le h_qhat_le_high_div)
    (n4CallAddbackBeqHighDivKnuthABound.of_le h_high_div_le_norm_plus_one)
    h_borrow

/-- Runtime-facing semantic bridge from direct qhat/high-div evidence parts.
    This is the final addback-side shape before the remaining high-div facts are
    discharged: no compact `RuntimeBounds`, `hq_over`, or remainder-bound
    premise is exposed. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_qhat_high_div_le_norm_plus_one_and_borrow
      hb3nz h_qhat_le_high_div h_high_div_le_norm_plus_one h_borrow)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_parts`. -/
theorem n4CallAddbackBeqSemanticHolds_of_runtime_qhat_high_div_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_parts
      hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one
      h_borrow h_carry2

/-- Runtime-facing semantic bridge from packaged direct qhat/high-div
    evidence. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqRuntimeQHatHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_parts
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeQHatHighDivEvidence.qhatHighDiv h_evidence)
    (n4CallAddbackBeqRuntimeQHatHighDivEvidence.knuthA h_evidence)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_evidence`. -/
theorem n4CallAddbackBeqSemanticHolds_of_runtime_qhat_high_div_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqRuntimeQHatHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_evidence
      hb3nz hshift_nz h_evidence h_borrow h_carry2

/-- Runtime-facing semantic bridge from raw direct qhat/high-div arithmetic
    facts via the compact evidence package. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_evidence
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeQHatHighDivEvidence.of_raw_parts
      h_qhat_le_high_div h_high_div_le_norm_plus_one)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_raw_parts`. -/
theorem n4CallAddbackBeqSemanticHolds_of_runtime_qhat_high_div_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_raw_parts
      hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one
      h_borrow h_carry2

/-- Runtime-facing semantic bridge from the larger shift/high-div evidence
    package via its compact qhat/high-div projection. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_evidence
    hb3nz hshift_nz
    (n4CallAddbackBeqShiftHighDivEvidence.toRuntimeQHatHighDivEvidence h_evidence)
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_evidence`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_high_div_runtime_qhat_evidence
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_evidence : n4CallAddbackBeqShiftHighDivEvidence a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_evidence
      hb3nz hshift_nz h_evidence h_borrow h_carry2

/-- Raw shift/high-div semantic bridge routed through the compact qhat/high-div
    package. The `rhatdd` fact remains in this compatibility-facing signature,
    but the semantic lowering itself only needs the direct qhat/high-div facts. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (_h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_raw_parts
    hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one
    h_borrow h_carry2

/-- Historical spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_raw_parts`. -/
theorem n4CallAddbackBeqSemanticHolds_of_shift_high_div_runtime_qhat_raw_parts
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_shift_high_div_runtime_qhat_raw_parts
      hb3nz hshift_nz h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Runtime semantic bridge from a direct qhat high-divisor bound and the
    weakened Knuth-A `+1` denominator bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_qhat_high_div_parts
    hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_qhat_high_div_le_norm_plus_one_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_qhat_le_high_div :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat)
    (h_high_div_le_norm_plus_one :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_qhat_high_div_le_norm_plus_one_and_borrow
      hb3nz hshift_nz h_qhat_le_high_div h_high_div_le_norm_plus_one h_borrow h_carry2

end EvmWord

end EvmAsm.Evm64
