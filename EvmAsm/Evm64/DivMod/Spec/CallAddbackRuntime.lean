/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime

  Runtime-condition bridges for the n=4 v4 call+addback semantic marker.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.CallAddback
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.Un21Bound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.UpperBound
public import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV4.ExactQuotient

@[expose] public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

/-- The packaged v4 n=4 call-addback runtime borrow predicate implies the raw
    addback branch condition consumed by `iterWithDoubleAddback`. -/
theorem n4CallAddbackBeqBorrow_raw_of_runtime {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    BitVec.ult (n4CallAddbackBeqU4 a b)
      (mulsubN4
        (n4CallAddbackBeqQHatV4 a b)
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)).2.2.2.2 := by
  rw [isAddbackBorrowN4CallV4Evm_def] at h_borrow
  unfold isAddbackBorrowN4CallV4Ab at h_borrow
  unfold loopBodyN4CallAddbackBorrowV4 at h_borrow
  simp_rw [divKTrialCallV4QHat_eq_div128Quot_v4] at h_borrow
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqQHatV4
    n4CallAddbackBeqShift n4CallAddbackBeqAntiShift
  by_cases h_branch :
      (a.getLimbN 3 >>>
        ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)).ult
        (mulsubN4_c3
          (div128Quot_v4
            (a.getLimbN 3 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
            (a.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
              a.getLimbN 2 >>>
                ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
            (b.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
              b.getLimbN 2 >>>
                ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
          (b.getLimbN 0 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (b.getLimbN 1 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 0 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (b.getLimbN 2 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 1 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (b.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            b.getLimbN 2 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 0 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64))
          (a.getLimbN 1 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 0 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 2 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 1 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64))
          (a.getLimbN 3 <<< ((clzResult (b.getLimbN 3)).1.toNat % 64) |||
            a.getLimbN 2 >>>
              ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)))
  · simpa [mulsubN4_c3] using h_branch
  · rw [if_neg h_branch] at h_borrow
    exact False.elim (h_borrow rfl)

/-- Runtime-borrow form of the addback iterator quotient bridge. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_runtime_borrow {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    (iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)).1 =
      n4CallAddbackBeqQOutV4 a b :=
  n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_borrow
    (n4CallAddbackBeqBorrow_raw_of_runtime h_borrow)

/-- The packaged v4 n=4 call-addback runtime carry2 predicate is the raw
    double-addback progress predicate over the normalized marker limbs. -/
theorem n4CallAddbackBeqCarry2Nz_of_runtime {a b : EvmWord}
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    isAddbackCarry2Nz
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b) := by
  have h_raw := isAddbackCarry2NzN4CallV4Evm_raw h_carry2
  simp_rw [divKTrialCallV4QHat_eq_div128Quot_v4] at h_raw
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  unfold isAddbackCarry2Nz
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqShift
    n4CallAddbackBeqAntiShift
  simpa using h_raw

/-- A nonzero original top divisor limb makes the normalized n=4 divisor
    nonzero, as required by double-addback value conservation. -/
theorem n4CallAddbackBeqNormalizedDivisor_ne_zero {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0 := by
  intro h_zero
  have h_b3_zero : n4CallAddbackBeqB3Prime b = 0 :=
    (BitVec.or_eq_zero_iff.mp h_zero).2
  have h_top_ge := n4CallAddbackBeqB3Prime_ge_pow63 hb3nz
  rw [h_b3_zero] at h_top_ge
  have h_zero_toNat : (0 : Word).toNat = 0 := by decide
  rw [h_zero_toNat] at h_top_ge
  norm_num at h_top_ge

/-- Positivity of the normalized n=4 divisor value from the original runtime
    top-limb nonzero condition. -/
theorem n4CallAddbackBeqNormalizedDivisor_pos {b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0) :
    0 < EvmWord.val256
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b) :=
  val256_pos_of_or_ne_zero (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)

/-- Normalized five-limb dividend value used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqUNormVal (a b : EvmWord) : Nat :=
  EvmWord.val256
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b) +
    (n4CallAddbackBeqU4 a b).toNat * 2^256

/-- Normalized divisor value used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqBNormVal (b : EvmWord) : Nat :=
  EvmWord.val256
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)

/-- Lower four limbs of the normalized dividend used by the v4 n=4 trial
    quotient bound. The overflow limb is tracked separately in `UNormVal`. -/
def n4CallAddbackBeqULoNormVal (a b : EvmWord) : Nat :=
  EvmWord.val256
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)

/-- Iterator output used by the v4 n=4 call-addback path. -/
def n4CallAddbackBeqIterOut (a b : EvmWord) :=
  iterWithDoubleAddback
    (n4CallAddbackBeqQHatV4 a b)
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)

/-- Normalized remainder value returned by the v4 n=4 call-addback iterator. -/
def n4CallAddbackBeqIterRNormVal (a b : EvmWord) : Nat :=
  let out := n4CallAddbackBeqIterOut a b
  EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
    out.2.2.2.2.2.toNat * 2^256

/-- Compact arithmetic obligations left after the runtime branch predicates:
    the v4 trial quotient is within one of the lower normalized quotient, and
    the corrected iterator remainder is below the normalized divisor. -/
def n4CallAddbackBeqRuntimeBounds (a b : EvmWord) : Prop :=
  (n4CallAddbackBeqQHatV4 a b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1 ∧
    n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b

/-- The normalized overflow dividend limb in the n=4 call-addback marker is
    strictly below `2^63` whenever normalization uses a nonzero shift. -/
theorem n4CallAddbackBeqU4_lt_pow63_of_shift_nz {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    (n4CallAddbackBeqU4 a b).toNat < 2^63 := by
  have h_shift_pos : 1 ≤ (clzResult (b.getLimbN 3)).1.toNat := by
    rcases Nat.eq_zero_or_pos (clzResult (b.getLimbN 3)).1.toNat with h | h
    · exfalso
      apply hshift_nz
      exact BitVec.eq_of_toNat_eq (by simp [h])
    · exact h
  have h :=
    u_top_lt_pow63_of_shift_nz
      (a.getLimbN 3) (clzResult (b.getLimbN 3)).1
      h_shift_pos (clzResult_fst_toNat_le (b.getLimbN 3))
  simpa [n4CallAddbackBeqU4, n4CallAddbackBeqAntiShift,
    n4CallAddbackBeqShift] using h

/-- The v4 Phase-1b `un21` intermediate is strictly below the normalized
    top divisor limb on the n=4 call path. -/
theorem n4CallAddbackBeqUn21_lt_b3prime_of_call {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (divKTrialCallV4Un21
      (n4CallAddbackBeqU4 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqB3Prime b)).toNat <
      (n4CallAddbackBeqB3Prime b).toNat := by
  have h :=
    un21V4_lt_vTop_of_call
      (a.getLimbN 2) (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)
      hb3nz hshift_nz hcall
  dsimp at h
  simpa [algorithmUn21V4, n4CallAddbackBeqU4, n4CallAddbackBeqU3,
    n4CallAddbackBeqB3Prime, n4CallAddbackBeqShift,
    n4CallAddbackBeqAntiShift] using h

/-- Decomposed-form `un21 < vTop` on the n=4 call path, with the raw
    `un21 < B3Prime` premise supplied internally. -/
theorem n4CallAddbackBeqUn21_lt_vTop_of_call {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (divKTrialCallV4Un21
      (n4CallAddbackBeqU4 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqB3Prime b)).toNat <
      (divKTrialCallV4DHi (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4DLo (n4CallAddbackBeqB3Prime b)).toNat :=
  n4CallAddbackBeqUn21_lt_vTop_of_lt_b3prime
    (n4CallAddbackBeqUn21_lt_b3prime_of_call hb3nz hshift_nz hcall)

/-- Trial-call half decomposition of the n=4 call-addback qhat on the call
    path, with the `un21` range proof supplied internally. -/
theorem n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_call_path
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3)) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      (divKTrialCallV4Q1dd
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat * 2^32 +
        (divKTrialCallV4Q0dd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b)).toNat :=
  n4CallAddbackBeqQHatV4_toNat_eq_trialCall_halves_of_call
    hb3nz hcall (n4CallAddbackBeqUn21_lt_vTop_of_call hb3nz hshift_nz hcall)

/-- Marker-name adapter for the v4 128/64 `+1` upper bound.

    This is not yet the compact `n4CallAddbackBeqRuntimeBounds` qhat
    obligation, whose denominator is the full normalized divisor. It exposes
    the proven 128/64 bound with `n4CallAddbackBeq*` names so the remaining
    runtime range and val256-denominator bridge can be attacked directly. -/
theorem n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_rhatdd_hi_zero {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hu4_lt_pow63 : (n4CallAddbackBeqU4 a b).toNat < 2^63)
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (hUn21_lt_b3prime :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (n4CallAddbackBeqB3Prime b).toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  have hu4_lt_b3prime :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v4_le_q_true_plus_one_of_rhatdd_hi_zero
    (n4CallAddbackBeqU4 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz)
    hu4_lt_b3prime
    hu4_lt_pow63
    hUn21_lt_pow63
    hUn21_lt_b3prime
    h_rhat_hi_zero

/-- Variant of `n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_rhatdd_hi_zero`
    with the normalized `U4 < 2^63` premise discharged from the nonzero
    normalization shift. -/
theorem n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_shift_nz_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (hUn21_lt_b3prime :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat <
        (n4CallAddbackBeqB3Prime b).toNat)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 :=
  n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_rhatdd_hi_zero
    hb3nz hcall (n4CallAddbackBeqU4_lt_pow63_of_shift_nz hshift_nz)
    hUn21_lt_pow63 hUn21_lt_b3prime h_rhat_hi_zero

/-- Variant of the marker qhat upper-bound adapter with the `U4 < 2^63`
    and `Un21 < B3Prime` premises discharged from the call-path and nonzero
    shift hypotheses. -/
theorem n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 :=
  n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_shift_nz_rhatdd_hi_zero
    hb3nz hshift_nz hcall hUn21_lt_pow63
    (n4CallAddbackBeqUn21_lt_b3prime_of_call hb3nz hshift_nz hcall)
    h_rhat_hi_zero

/-- Marker-name adapter for the floor-shaped v4 128/64 `+1` upper bound
    in the call-path, final high-half-zero branch. This is the same numeric
    bound as the older `128_div` adapter, but routed through the floor-named
    surface consumed by the Knuth-A/qhat path. -/
theorem n4CallAddbackBeqQHatV4_le_floor_plus_one_of_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word)) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat + 1 := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized]
  have hu4_lt_b3prime :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v4_le_floor_plus_one_of_rhatdd_hi_zero
    (n4CallAddbackBeqU4 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz)
    hu4_lt_b3prime
    (n4CallAddbackBeqU4_lt_pow63_of_shift_nz hshift_nz)
    hUn21_lt_pow63
    (n4CallAddbackBeqUn21_lt_b3prime_of_call hb3nz hshift_nz hcall)
    h_rhat_hi_zero

/-- Marker-name adapter for exact v4 128/64 floor qhat evidence in the
    call-path final high-half-zero branch.

    The matching upper bound is intentionally explicit: this is the evidence
    that future exact-quotient work should discharge before applying the
    weaker normalized `+1` bridge. -/
theorem n4CallAddbackBeqQHatV4_eq_floor_of_call_rhatdd_hi_zero_of_le
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
    (h_le :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
            (n4CallAddbackBeqU3 a b).toNat) /
          (n4CallAddbackBeqB3Prime b).toNat) :
    (n4CallAddbackBeqQHatV4 a b).toNat =
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat := by
  rw [n4CallAddbackBeqQHatV4_eq_normalized] at h_le ⊢
  have hu4_lt_b3prime :
      (n4CallAddbackBeqU4 a b).toNat < (n4CallAddbackBeqB3Prime b).toNat := by
    have h_decomp := n4CallAddbackBeqU4_lt_vTop_of_call hcall
    rw [div128Quot_vTop_decomp (n4CallAddbackBeqB3Prime b)]
    simpa [divKTrialCallV4DHi, divKTrialCallV4DLo] using h_decomp
  exact div128Quot_v4_eq_floor_of_rhatdd_hi_zero_of_le
    (n4CallAddbackBeqU4 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqB3Prime_ge_pow63 hb3nz)
    hu4_lt_b3prime
    (n4CallAddbackBeqU4_lt_pow63_of_shift_nz hshift_nz)
    (n4CallAddbackBeqUn21_lt_b3prime_of_call hb3nz hshift_nz hcall)
    h_rhat_hi_zero
    h_le

/-- Reduce the compact runtime qhat bound to the remaining denominator bridge.

    The v4 128/64 qhat bound is already discharged by the call path,
    `hUn21_lt_pow63`, and the `rhatdd` high-half-zero branch. What remains
    for `n4CallAddbackBeqRuntimeBounds` is the Knuth-A bridge from the high
    128/64 quotient denominator to the full normalized 256-bit divisor. -/
theorem n4CallAddbackBeqQHatV4_le_norm_div_plus_one_of_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_high_div_le_norm :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1 := by
  have h_qhat_high :=
    n4CallAddbackBeqQHatV4_le_128_div_plus_one_of_call_rhatdd_hi_zero
      hb3nz hshift_nz hcall hUn21_lt_pow63 h_rhat_hi_zero
  omega

/-- Floor-named variant of the compact runtime qhat bound reduction.

    This keeps the normalized-divisor bridge phrased over the floor-shaped
    upper-bound adapter, matching the N4 Knuth-A path while leaving the
    remaining high-divisor-to-normalized-divisor premise explicit. -/
theorem n4CallAddbackBeqQHatV4_le_norm_div_plus_one_of_floor_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_high_div_le_norm :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b) :
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1 := by
  have h_qhat_high :=
    n4CallAddbackBeqQHatV4_le_floor_plus_one_of_call_rhatdd_hi_zero
      hb3nz hshift_nz hcall hUn21_lt_pow63 h_rhat_hi_zero
  omega

/-- Exact-floor qhat evidence plus the correct Knuth-A `+1` denominator
    bridge gives the compact normalized qhat runtime bound.

    This is the shape left viable by the v4 counterexample: the high 128/64
    quotient need not be below the lower normalized quotient, but it may be
    within one of it. -/
theorem n4CallAddbackBeqQHatV4_le_norm_div_plus_one_of_floor_eq
    {a b : EvmWord}
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
    (n4CallAddbackBeqQHatV4 a b).toNat ≤
      n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1 := by
  omega

/-- Runtime-normalized c3 bridge: if the normalized trial quotient is within
    one of the normalized true quotient, the raw borrow condition pins the
    mulsub carry-out to one. -/
theorem n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_one {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2) :
      (mulsubN4
        (n4CallAddbackBeqQHatV4 a b)
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)).2.2.2.2 = 1 := by
  apply mulsubN4_c3_ne_zero_imp_one hbnz hq_over
  intro h_zero
  rw [h_zero] at h_borrow
  simp [BitVec.ult] at h_borrow

/-- Runtime-condition wrapper for double-addback value conservation over the
    normalized n=4 v4 call+addback marker limbs. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 →
        (mulsubN4
          (n4CallAddbackBeqQHatV4 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 = 1)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)
    EvmWord.val256
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2^256 =
      out.1.toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  exact iterWithDoubleAddback_val256_conservation_of_carry2
    (n4CallAddbackBeqQHatV4 a b)
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)
    hbnz
    hc3_one_of_borrow
    (n4CallAddbackBeqCarry2Nz_of_runtime h_carry2)

/-- Runtime-condition value conservation using a normalized `qHat ≤ qTrue + 1`
    bound to discharge the c3=1-on-borrow side condition. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_one
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)
    EvmWord.val256
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2^256 =
      out.1.toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime
    hbnz
    (n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_one hbnz hq_over)
    h_carry2

/-- Runtime-condition value conservation with the original top-limb nonzero
    runtime condition discharging normalized divisor nonzero. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)
    EvmWord.val256
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2^256 =
      out.1.toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_one
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    hq_over
    h_carry2

/-- Runtime-condition normalized remainder bound for the n=4 call+addback-BEQ
    path, stated over the normalized marker limbs. -/
theorem n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtime
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b := by
  have hb := n4CallAddbackBeqBorrow_raw_of_runtime h_borrow
  have hc3_one :=
    n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_one
      hbnz hq_over hb
  have h := iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_one
    (n4CallAddbackBeqQHatV4 a b)
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)
    hbnz hb hc3_one hq_over
  simpa [n4CallAddbackBeqIterRNormVal, n4CallAddbackBeqIterOut,
    n4CallAddbackBeqBNormVal] using h

/-- Runtime-condition normalized remainder bound with the original top-limb
    nonzero condition discharging normalized divisor nonzero. -/
theorem n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b :=
  n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtime
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    (by
      simpa [n4CallAddbackBeqULoNormVal, n4CallAddbackBeqBNormVal] using hq_over)
    h_borrow

/-- Package the compact n=4 call+addback-BEQ runtime bounds from the qhat
    bound and the runtime borrow predicate. -/
theorem n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  ⟨hq_over,
    n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtime_top_nonzero
      hb3nz hq_over h_borrow⟩

/-- Runtime-condition value conservation with the iterator quotient rewritten
    to the named v4 call-addback quotient output. -/
theorem n4CallAddbackBeqQOutV4_val256_conservation_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV4 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)
    EvmWord.val256
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b) +
      (n4CallAddbackBeqU4 a b).toNat * 2^256 =
      (n4CallAddbackBeqQOutV4 a b).toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  have h := n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzero
    hb3nz hq_over h_carry2
  dsimp only at h ⊢
  rw [n4CallAddbackBeqIterWithDoubleAddback_qOutV4_of_runtime_borrow h_borrow] at h
  exact h

/-- Compact form of the runtime-condition value conservation theorem. -/
theorem n4CallAddbackBeqQOutV4_conservation_compact
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqUNormVal a b =
      (n4CallAddbackBeqQOutV4 a b).toNat * n4CallAddbackBeqBNormVal b +
        n4CallAddbackBeqIterRNormVal a b := by
  have h := n4CallAddbackBeqQOutV4_val256_conservation_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2
  dsimp [n4CallAddbackBeqUNormVal, n4CallAddbackBeqBNormVal,
    n4CallAddbackBeqIterRNormVal, n4CallAddbackBeqIterOut] at h ⊢
  simpa [Nat.add_assoc] using h

/-- Pure quotient extraction for the call-addback conservation shape. -/
theorem quotient_eq_div_of_mul_add_remainder_lt {aVal bVal qVal rVal : Nat}
    (hb_pos : 0 < bVal)
    (h_eq : aVal = qVal * bVal + rVal)
    (h_rem_lt : rVal < bVal) :
    qVal = aVal / bVal := by
  rw [h_eq]
  rw [Nat.add_comm]
  rw [Nat.add_mul_div_right _ _ hb_pos]
  rw [Nat.div_eq_of_lt h_rem_lt]
  rw [Nat.zero_add]

/-- Runtime-condition quotient extraction from the compact conservation shape,
    assuming the compact normalized remainder is below the normalized divisor. -/
theorem n4CallAddbackBeqQOutV4_toNat_eq_normalized_div_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    (n4CallAddbackBeqQOutV4 a b).toNat =
      n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b := by
  exact quotient_eq_div_of_mul_add_remainder_lt
    (by
      simpa [n4CallAddbackBeqBNormVal] using
        n4CallAddbackBeqNormalizedDivisor_pos hb3nz)
    (n4CallAddbackBeqQOutV4_conservation_compact
      hb3nz hq_over h_borrow h_carry2)
    h_rem_lt

/-- The compact normalized quotient target is the original unnormalized
    `qTrue`, since both dividend and divisor were scaled by the same CLZ
    normalization factor. -/
theorem n4CallAddbackBeqNormalized_div_eq_qTrue
    {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b =
      n4CallAddbackBeqQTrue a b := by
  have h_norm_u := u_val256_eq_scaled_with_overflow
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 3) hshift_nz
  have h_norm_b := b3_prime_val256_eq_scaled
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    hshift_nz
  rw [n4CallAddbackBeqQTrue_unfold]
  rw [n4CallAddbackBeqUNormVal, n4CallAddbackBeqBNormVal]
  rw [n4CallAddbackBeqU0_unfold, n4CallAddbackBeqU1_unfold,
    n4CallAddbackBeqU2_unfold, n4CallAddbackBeqU3_unfold,
    n4CallAddbackBeqU4_unfold, n4CallAddbackBeqB0Prime_unfold,
    n4CallAddbackBeqB1Prime_unfold, n4CallAddbackBeqB2Prime_unfold,
    n4CallAddbackBeqB3Prime_unfold, n4CallAddbackBeqShift_unfold,
    n4CallAddbackBeqAntiShift_unfold]
  rw [h_norm_u, h_norm_b]
  exact val256_div_scale_invariant
    (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    (clzResult (b.getLimbN 3)).1.toNat

/-- Runtime-condition semantic bridge after the normalized quotient target has
    been identified with the original unnormalized `qTrue`. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b)
    (h_norm_div :
      n4CallAddbackBeqUNormVal a b / n4CallAddbackBeqBNormVal b =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b := by
  apply n4CallAddbackBeqSemanticHoldsV4_of_qOutV4_toNat_eq_qTrue
  rw [n4CallAddbackBeqQOutV4_toNat_eq_normalized_div_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt]
  exact h_norm_div

/-- Runtime-condition semantic bridge after discharging the normalized-divisor
    scaling step from the CLZ shift nonzero condition. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt
    (n4CallAddbackBeqNormalized_div_eq_qTrue hshift_nz)

/-- Historical non-`V4` spelling of the runtime-condition closure for the
    repaired n=4 call+addback-BEQ semantic marker. -/
theorem n4CallAddbackBeqSemanticHolds_of_runtime_conditions
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        EvmWord.val256
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b) /
          EvmWord.val256
            (n4CallAddbackBeqB0Prime b)
            (n4CallAddbackBeqB1Prime b)
            (n4CallAddbackBeqB2Prime b)
            (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions
      hb3nz hshift_nz hq_over h_borrow h_carry2 h_rem_lt

/-- Compact runtime-condition semantic bridge with the qhat-over side
    condition stated using named normalized values. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions_compact
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormVal a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions
    hb3nz hshift_nz
    (by
      simpa [n4CallAddbackBeqULoNormVal, n4CallAddbackBeqBNormVal] using hq_over)
    h_borrow h_carry2 h_rem_lt

/-- Runtime-condition semantic bridge with the remaining compact arithmetic
    bounds bundled as one named predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions_compact
    hb3nz hshift_nz h_bounds.1 h_borrow h_carry2 h_bounds.2

/-- Runtime semantic bridge with the normalized remainder bound discharged from
    the qhat bound and runtime borrow predicate. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_qhat_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
      hb3nz hq_over h_borrow)
    h_borrow h_carry2

/-- Runtime-bounds package from exact-floor qhat evidence, the weakened
    Knuth-A `+1` denominator bridge, and the runtime borrow predicate. -/
theorem n4CallAddbackBeqRuntimeBounds_of_floor_eq_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
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
  n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatV4_le_norm_div_plus_one_of_floor_eq
      h_floor h_high_div_le_norm_plus_one)
    h_borrow

/-- Runtime semantic bridge from exact-floor qhat evidence and the weakened
    Knuth-A `+1` denominator bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
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
    (n4CallAddbackBeqRuntimeBounds_of_floor_eq_and_borrow
      hb3nz h_floor h_high_div_le_norm_plus_one h_borrow)
    h_borrow h_carry2

/-- Runtime-bounds package from the call-path exact-floor adapter and the
    weakened Knuth-A `+1` denominator bridge. -/
theorem n4CallAddbackBeqRuntimeBounds_of_exact_floor_call_rhatdd_hi_zero_and_borrow
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
  n4CallAddbackBeqRuntimeBounds_of_floor_eq_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatV4_eq_floor_of_call_rhatdd_hi_zero_of_le
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_le_high_div)
    h_high_div_le_norm_plus_one
    h_borrow

/-- Runtime semantic bridge from the call-path exact-floor adapter and the
    weakened Knuth-A `+1` denominator bridge. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_exact_floor_call_rhatdd_hi_zero
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
    (n4CallAddbackBeqRuntimeBounds_of_exact_floor_call_rhatdd_hi_zero_and_borrow
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_floor_eq_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_floor :
      (n4CallAddbackBeqQHatV4 a b).toNat =
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
    n4CallAddbackBeqSemanticHoldsV4_of_floor_eq_and_borrow
      hb3nz hshift_nz h_floor h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_exact_floor_call_rhatdd_hi_zero`. -/
theorem n4CallAddbackBeqSemanticHolds_of_exact_floor_call_rhatdd_hi_zero
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
    n4CallAddbackBeqSemanticHoldsV4_of_exact_floor_call_rhatdd_hi_zero
      hb3nz hshift_nz hcall h_rhat_hi_zero h_qhat_le_high_div
      h_high_div_le_norm_plus_one h_borrow h_carry2

/-- Runtime-bounds package from the floor-named qhat upper-bound path and
    the runtime borrow predicate.

    This packages the two compact arithmetic facts consumed by the semantic
    bridge: the normalized qhat `+1` upper bound and the corresponding
    normalized remainder bound after the double-addback path. -/
theorem n4CallAddbackBeqRuntimeBounds_of_floor_call_rhatdd_hi_zero_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_high_div_le_norm :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b) :
    n4CallAddbackBeqRuntimeBounds a b :=
  n4CallAddbackBeqRuntimeBounds_of_qhat_bound_and_borrow
    hb3nz
    (n4CallAddbackBeqQHatV4_le_norm_div_plus_one_of_floor_call_rhatdd_hi_zero
      hb3nz hshift_nz hcall hUn21_lt_pow63 h_rhat_hi_zero
      h_high_div_le_norm)
    h_borrow

/-- Runtime semantic bridge using the floor-named qhat upper-bound path.

    The remaining explicit arithmetic premise is exactly the Knuth-A
    high-divisor-to-normalized-divisor bridge. The qhat bound and remainder
    runtime bounds are then derived internally. -/
theorem n4CallAddbackBeqSemanticHoldsV4_of_floor_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_high_div_le_norm :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHoldsV4 a b :=
  n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
    hb3nz hshift_nz
    (n4CallAddbackBeqRuntimeBounds_of_floor_call_rhatdd_hi_zero_and_borrow
      hb3nz hshift_nz hcall hUn21_lt_pow63 h_rhat_hi_zero
      h_high_div_le_norm h_borrow)
    h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_floor_call_rhatdd_hi_zero`. -/
theorem n4CallAddbackBeqSemanticHolds_of_floor_call_rhatdd_hi_zero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hcall : isCallTrialN4 (a.getLimbN 3) (b.getLimbN 2) (b.getLimbN 3))
    (hUn21_lt_pow63 :
      (divKTrialCallV4Un21
        (n4CallAddbackBeqU4 a b)
        (n4CallAddbackBeqU3 a b)
        (n4CallAddbackBeqB3Prime b)).toNat < 2^63)
    (h_rhat_hi_zero :
      divKTrialCallV4Rhatdd
          (n4CallAddbackBeqU4 a b)
          (n4CallAddbackBeqU3 a b)
          (n4CallAddbackBeqB3Prime b) >>> (32 : BitVec 6).toNat =
        (0 : Word))
    (h_high_div_le_norm :
      ((n4CallAddbackBeqU4 a b).toNat * 2^64 +
          (n4CallAddbackBeqU3 a b).toNat) /
        (n4CallAddbackBeqB3Prime b).toNat ≤
          n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_floor_call_rhatdd_hi_zero
      hb3nz hshift_nz hcall hUn21_lt_pow63 h_rhat_hi_zero
      h_high_div_le_norm h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds`. -/
theorem n4CallAddbackBeqSemanticHolds_of_runtime_bounds
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (h_bounds : n4CallAddbackBeqRuntimeBounds a b)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_runtime_bounds
      hb3nz hshift_nz h_bounds h_borrow h_carry2

/-- Historical non-`V4` spelling of
    `n4CallAddbackBeqSemanticHoldsV4_of_qhat_bound_and_borrow`. -/
theorem n4CallAddbackBeqSemanticHolds_of_qhat_bound_and_borrow
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV4 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV4Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV4Evm a b) :
    n4CallAddbackBeqSemanticHolds a b := by
  simpa [n4CallAddbackBeqSemanticHolds_eq_v4] using
    n4CallAddbackBeqSemanticHoldsV4_of_qhat_bound_and_borrow
      hb3nz hshift_nz hq_over h_borrow h_carry2

/-- **n4 call+addback (shift≠0) getLimbN bridge.**
    Under `n4CallAddbackBeqSemanticHolds a b` (the algorithm's q_out equals the
    true quotient) and `b.getLimbN 3 ≠ 0` (n=4, so val256(b) ≥ 2^192 and the
    quotient fits in one 64-bit limb), the DIV result has
    `getLimbN 0 = n4CallAddbackBeqQOutV4 a b` and all upper limbs zero.

    Used to bridge `evm_div_n4_full_call_addback_beq_spec_noNop`'s output
    (which gives `fullDivN4CallAddbackBeqPost`) toward the public EVM-stack post
    with `EvmWord.div a b` in the quotient slot. -/
theorem n4_call_addback_beq_div_getLimbN (a b : EvmWord)
    (hbnz : b ≠ 0)
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hsem : n4CallAddbackBeqSemanticHolds a b) :
    (EvmWord.div a b).getLimbN 0 = n4CallAddbackBeqQOutV4 a b ∧
    (EvmWord.div a b).getLimbN 1 = 0 ∧
    (EvmWord.div a b).getLimbN 2 = 0 ∧
    (EvmWord.div a b).getLimbN 3 = 0 := by
  -- Step 1: Convert SemanticHolds to V4 form: QOutV4.toNat = QTrue = val256(a)/val256(b)
  have hsemV4 := n4CallAddbackBeqSemanticHolds_v4 hsem
  unfold n4CallAddbackBeqSemanticHoldsV4 n4CallAddbackBeqQTrue at hsemV4
  -- Step 2: Connect val256 to toNat
  have ha_val : val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) = a.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat a
  have hb_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) = b.toNat := by
    simp only [← getLimb_as_getLimbN_0, ← getLimb_as_getLimbN_1,
               ← getLimb_as_getLimbN_2, ← getLimb_as_getLimbN_3]
    exact val256_eq_toNat b
  rw [ha_val, hb_val] at hsemV4
  -- Step 3: EvmWord.div a b = a.toNat / b.toNat
  have hdiv_toNat : (EvmWord.div a b).toNat = a.toNat / b.toNat := by
    unfold EvmWord.div; rw [if_neg hbnz]; exact BitVec.toNat_udiv
  -- Step 4: QOutV4.toNat = (EvmWord.div a b).toNat
  have hq_toNat : (n4CallAddbackBeqQOutV4 a b).toNat = (EvmWord.div a b).toNat := by omega
  -- Step 5: Quotient fits in one limb since b.getLimbN 3 ≠ 0 → b ≥ 2^192
  have hb_gt : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h])) hbnz
    · exact h
  have hb3_val : val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) ≥ 2^192 :=
    val256_ge_pow192_of_limb3 _ _ _ _ hb3nz
  rw [hb_val] at hb3_val
  have hqlt : (n4CallAddbackBeqQOutV4 a b).toNat < 2^64 := by
    rw [hq_toNat, hdiv_toNat]
    have hbnd := val256_bound (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3)
    rw [ha_val] at hbnd
    calc a.toNat / b.toNat ≤ (2^256 - 1) / b.toNat := Nat.div_le_div_right (by omega)
      _ ≤ (2^256 - 1) / 2^192 := Nat.div_le_div_left hb3_val (by omega)
      _ = 2^64 - 1 := by norm_num
      _ < 2^64 := by omega
  -- Step 6: Build the target EvmWord (QOutV4 in limb 0, zeros elsewhere) = EvmWord.div a b
  set q := n4CallAddbackBeqQOutV4 a b with hq_def
  set target := EvmWord.fromLimbs (fun i : Fin 4 =>
    match i with | 0 => q | 1 => 0 | 2 => 0 | 3 => 0) with htarget_def
  have htarget_toNat : target.toNat = q.toNat := by
    simp [htarget_def, EvmWord.fromLimbs_toNat]
  have htarget_eq_div : target = EvmWord.div a b :=
    BitVec.eq_of_toNat_eq (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_0
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_1
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_2
  · rw [← htarget_eq_div]; exact getLimbN_fromLimbs_3

end EvmWord

end EvmAsm.Evm64
