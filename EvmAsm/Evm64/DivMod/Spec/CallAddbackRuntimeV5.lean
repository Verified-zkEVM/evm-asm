/-
  EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntimeV5

  V5 mirror of the hq_over-ASSUMING runtime-condition chain that culminates in
  `n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy`.

  This is the V5 analogue of the chain in
  `EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime` that ends in
  `n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions`.  It takes the
  `hq_over` trial-quotient bound as a HYPOTHESIS (discharging it unconditionally
  is a separate bead).

  Only the lemmas that mention the V5-specific predicates
  (`QHatV5`/`QOutV5`/`CarryV5`/`SemanticHoldsV5`/`isAddbackBorrowN4CallV5Evm`/
  `isAddbackCarry2NzN4CallV5Evm`) are re-proved here; the version-agnostic
  helpers (the B'/U normalized limbs, `mulsubN4`, `addbackN4_carry`,
  `iterWithDoubleAddback`, `n4CallAddbackBeqQTrue`, `BNormVal`, `ULoNormVal`,
  `n4CallAddbackBeqNormalized_div_eq_qTrue`, …) are reused directly from
  `CallAddbackRuntime`.

  The repaired trial-quotient bridge `divKTrialCallV5QHat_eq_div128Quot_v5`
  (from `CallSkipLowerBoundV5.UpperBound`) is the V5 analogue of
  `divKTrialCallV4QHat_eq_div128Quot_v4`.
-/

import EvmAsm.Evm64.DivMod.Spec.CallAddbackV5
import EvmAsm.Evm64.DivMod.Spec.CallAddbackRuntime
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.UpperBound

namespace EvmAsm.Evm64

open EvmAsm.Rv64

namespace EvmWord

-- ============================================================================
-- V5 raw-predicate extraction (mirrors `isAddbackCarry2NzN4CallV4Evm_raw`)
-- ============================================================================

/-- Eliminate the packaged EvmWord v5 n=4 call-addback carry2 predicate to the
    raw implication consumed by double-addback loop-body proofs. -/
theorem isAddbackCarry2NzN4CallV5Evm_raw {a b : EvmWord}
    (hcarry2_nz : isAddbackCarry2NzN4CallV5Evm a b) :
    let shift := (clzResult (b.getLimbN 3)).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := ((b.getLimbN 3) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 2) >>> (antiShift.toNat % 64))
    let b2' := ((b.getLimbN 2) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 1) >>> (antiShift.toNat % 64))
    let b1' := ((b.getLimbN 1) <<< (shift.toNat % 64)) |||
      ((b.getLimbN 0) >>> (antiShift.toNat % 64))
    let b0' := (b.getLimbN 0) <<< (shift.toNat % 64)
    let u4 := (a.getLimbN 3) >>> (antiShift.toNat % 64)
    let u3 := ((a.getLimbN 3) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 2) >>> (antiShift.toNat % 64))
    let u2 := ((a.getLimbN 2) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 1) >>> (antiShift.toNat % 64))
    let u1 := ((a.getLimbN 1) <<< (shift.toNat % 64)) |||
      ((a.getLimbN 0) >>> (antiShift.toNat % 64))
    let u0 := (a.getLimbN 0) <<< (shift.toNat % 64)
    let qHat := divKTrialCallV5QHat u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let c3 := ms.2.2.2.2
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let ab := addbackN4 ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 (u4 - c3) b0' b1' b2' b3'
    carry = 0 →
      addbackN4_carry ab.1 ab.2.1 ab.2.2.1 ab.2.2.2.1 b0' b1' b2' b3' ≠ 0 := by
  rw [isAddbackCarry2NzN4CallV5Evm_def] at hcarry2_nz
  unfold isAddbackCarry2NzN4CallV5Ab at hcarry2_nz
  unfold loopBodyN4CallAddbackCarry2NzV5 at hcarry2_nz
  simpa using hcarry2_nz

-- ============================================================================
-- V5 borrow / carry2 runtime → raw-condition bridges
-- ============================================================================

/-- The packaged v5 n=4 call-addback runtime borrow predicate implies the raw
    addback branch condition consumed by `iterWithDoubleAddback`. -/
theorem n4CallAddbackBeqBorrow_raw_of_runtimeV5 {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    BitVec.ult (n4CallAddbackBeqU4 a b)
      (mulsubN4
        (n4CallAddbackBeqQHatV5 a b)
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b)
        (n4CallAddbackBeqU0 a b)
        (n4CallAddbackBeqU1 a b)
        (n4CallAddbackBeqU2 a b)
        (n4CallAddbackBeqU3 a b)).2.2.2.2 := by
  rw [isAddbackBorrowN4CallV5Evm_def] at h_borrow
  unfold isAddbackBorrowN4CallV5Ab at h_borrow
  unfold loopBodyN4CallAddbackBorrowV5 at h_borrow
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5] at h_borrow
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqQHatV5
    n4CallAddbackBeqShift n4CallAddbackBeqAntiShift
  by_cases h_branch :
      (a.getLimbN 3 >>>
        ((signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64)).ult
        (mulsubN4_c3
          (div128Quot_v5
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

/-- The packaged v5 n=4 call-addback runtime carry2 predicate is the raw
    double-addback progress predicate over the normalized marker limbs. -/
theorem n4CallAddbackBeqCarry2Nz_of_runtimeV5 {a b : EvmWord}
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    isAddbackCarry2Nz
      (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b) := by
  have h_raw := isAddbackCarry2NzN4CallV5Evm_raw h_carry2
  simp_rw [divKTrialCallV5QHat_eq_div128Quot_v5] at h_raw
  rw [n4CallAddbackBeqQHatV5_eq_normalized]
  unfold isAddbackCarry2Nz
  unfold n4CallAddbackBeqB0Prime n4CallAddbackBeqB1Prime
    n4CallAddbackBeqB2Prime n4CallAddbackBeqB3Prime
    n4CallAddbackBeqU0 n4CallAddbackBeqU1 n4CallAddbackBeqU2
    n4CallAddbackBeqU3 n4CallAddbackBeqU4 n4CallAddbackBeqShift
    n4CallAddbackBeqAntiShift
  simpa using h_raw

/-- Runtime-borrow form of the addback iterator quotient bridge. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_runtime_borrow {a b : EvmWord}
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    (iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
      (n4CallAddbackBeqB0Prime b)
      (n4CallAddbackBeqB1Prime b)
      (n4CallAddbackBeqB2Prime b)
      (n4CallAddbackBeqB3Prime b)
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b)
      (n4CallAddbackBeqU4 a b)).1 =
      n4CallAddbackBeqQOutV5 a b :=
  n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_borrow
    (n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow)

-- ============================================================================
-- V5 normalized iterator / remainder values
-- ============================================================================

/-- Iterator output used by the v5 n=4 call-addback path. -/
def n4CallAddbackBeqIterOutV5 (a b : EvmWord) :=
  iterWithDoubleAddback
    (n4CallAddbackBeqQHatV5 a b)
    (n4CallAddbackBeqB0Prime b)
    (n4CallAddbackBeqB1Prime b)
    (n4CallAddbackBeqB2Prime b)
    (n4CallAddbackBeqB3Prime b)
    (n4CallAddbackBeqU0 a b)
    (n4CallAddbackBeqU1 a b)
    (n4CallAddbackBeqU2 a b)
    (n4CallAddbackBeqU3 a b)
    (n4CallAddbackBeqU4 a b)

/-- Normalized remainder value returned by the v5 n=4 call-addback iterator. -/
def n4CallAddbackBeqIterRNormValV5 (a b : EvmWord) : Nat :=
  let out := n4CallAddbackBeqIterOutV5 a b
  EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
    out.2.2.2.2.2.toNat * 2^256

/-- Normalized five-limb dividend value used by the v5 n=4 call-addback path.
    (Structurally identical to the v4 `UNormVal`; restated for the V5 names.) -/
def n4CallAddbackBeqUNormValV5 (a b : EvmWord) : Nat :=
  EvmWord.val256
      (n4CallAddbackBeqU0 a b)
      (n4CallAddbackBeqU1 a b)
      (n4CallAddbackBeqU2 a b)
      (n4CallAddbackBeqU3 a b) +
    (n4CallAddbackBeqU4 a b).toNat * 2^256

-- ============================================================================
-- V5 c3-on-borrow bridge
-- ============================================================================

/-- Runtime-normalized c3 bridge: if the normalized trial quotient is within
    one of the normalized true quotient, the raw borrow condition pins the
    mulsub carry-out to one. -/
theorem n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_oneV5 {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
          (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2) :
      (mulsubN4
        (n4CallAddbackBeqQHatV5 a b)
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

-- ============================================================================
-- V5 double-addback value conservation chain
-- ============================================================================

/-- Runtime-condition wrapper for double-addback value conservation over the
    normalized n=4 v5 call+addback marker limbs. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtimeV5
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hc3_one_of_borrow :
      BitVec.ult (n4CallAddbackBeqU4 a b)
        (mulsubN4
          (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 →
        (mulsubN4
          (n4CallAddbackBeqQHatV5 a b)
          (n4CallAddbackBeqB0Prime b)
          (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b)
          (n4CallAddbackBeqB3Prime b)
          (n4CallAddbackBeqU0 a b)
          (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b)
          (n4CallAddbackBeqU3 a b)).2.2.2.2 = 1)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
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
    (n4CallAddbackBeqQHatV5 a b)
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
    (n4CallAddbackBeqCarry2Nz_of_runtimeV5 h_carry2)

/-- Runtime-condition value conservation using a normalized `qHat ≤ qTrue + 1`
    bound to discharge the c3=1-on-borrow side condition. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_oneV5
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
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
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtimeV5
    hbnz
    (n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_oneV5 hbnz hq_over)
    h_carry2

/-- Runtime-condition value conservation with the original top-limb nonzero
    runtime condition discharging normalized divisor nonzero. -/
theorem n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzeroV5
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
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
  exact n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_qhat_le_div_plus_oneV5
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    hq_over
    h_carry2

-- ============================================================================
-- V5 normalized remainder bound
-- ============================================================================

/-- Runtime-condition normalized remainder bound for the n=4 v5 call+addback-BEQ
    path, stated over the normalized marker limbs. -/
theorem n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtimeV5
    {a b : EvmWord}
    (hbnz :
      n4CallAddbackBeqB0Prime b ||| n4CallAddbackBeqB1Prime b |||
        n4CallAddbackBeqB2Prime b ||| n4CallAddbackBeqB3Prime b ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b := by
  have hb := n4CallAddbackBeqBorrow_raw_of_runtimeV5 h_borrow
  have hc3_one :=
    n4CallAddbackBeqC3_eq_one_of_borrow_and_qhat_le_div_plus_oneV5
      hbnz hq_over hb
  have h := iterWithDoubleAddback_borrow_remainder_lt_of_qhat_le_div_plus_one
    (n4CallAddbackBeqQHatV5 a b)
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
  simpa [n4CallAddbackBeqIterRNormValV5, n4CallAddbackBeqIterOutV5,
    n4CallAddbackBeqBNormVal] using h

/-- Runtime-condition normalized remainder bound with the original top-limb
    nonzero condition discharging normalized divisor nonzero. -/
theorem n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtime_top_nonzeroV5
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
        n4CallAddbackBeqULoNormVal a b / n4CallAddbackBeqBNormVal b + 1)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b) :
    n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b :=
  n4CallAddbackBeqIterRNormVal_lt_BNormVal_of_runtimeV5
    (n4CallAddbackBeqNormalizedDivisor_ne_zero hb3nz)
    (by
      simpa [n4CallAddbackBeqULoNormVal, n4CallAddbackBeqBNormVal] using hq_over)
    h_borrow

-- ============================================================================
-- V5 qOut value conservation
-- ============================================================================

/-- Runtime-condition value conservation with the iterator quotient rewritten
    to the named v5 call-addback quotient output. -/
theorem n4CallAddbackBeqQOutV5_val256_conservation_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    let out := iterWithDoubleAddback
      (n4CallAddbackBeqQHatV5 a b)
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
      (n4CallAddbackBeqQOutV5 a b).toNat * EvmWord.val256
        (n4CallAddbackBeqB0Prime b)
        (n4CallAddbackBeqB1Prime b)
        (n4CallAddbackBeqB2Prime b)
        (n4CallAddbackBeqB3Prime b) +
      EvmWord.val256 out.2.1 out.2.2.1 out.2.2.2.1 out.2.2.2.2.1 +
      out.2.2.2.2.2.toNat * 2^256 := by
  have h := n4CallAddbackBeqIterWithDoubleAddback_val256_conservation_of_runtime_top_nonzeroV5
    hb3nz hq_over h_carry2
  dsimp only at h ⊢
  rw [n4CallAddbackBeqIterWithDoubleAddback_qOutV5_of_runtime_borrow h_borrow] at h
  exact h

/-- Compact form of the runtime-condition value conservation theorem. -/
theorem n4CallAddbackBeqQOutV5_conservation_compact
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b) :
    n4CallAddbackBeqUNormValV5 a b =
      (n4CallAddbackBeqQOutV5 a b).toNat * n4CallAddbackBeqBNormVal b +
        n4CallAddbackBeqIterRNormValV5 a b := by
  have h := n4CallAddbackBeqQOutV5_val256_conservation_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2
  dsimp [n4CallAddbackBeqUNormValV5, n4CallAddbackBeqBNormVal,
    n4CallAddbackBeqIterRNormValV5, n4CallAddbackBeqIterOutV5] at h ⊢
  simpa [Nat.add_assoc] using h

-- ============================================================================
-- V5 quotient extraction and semantic bridge
-- ============================================================================

/-- Runtime-condition quotient extraction from the compact conservation shape,
    assuming the compact normalized remainder is below the normalized divisor. -/
theorem n4CallAddbackBeqQOutV5_toNat_eq_normalized_div_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b) :
    (n4CallAddbackBeqQOutV5 a b).toNat =
      n4CallAddbackBeqUNormValV5 a b / n4CallAddbackBeqBNormVal b := by
  exact quotient_eq_div_of_mul_add_remainder_lt
    (by
      simpa [n4CallAddbackBeqBNormVal] using
        n4CallAddbackBeqNormalizedDivisor_pos hb3nz)
    (n4CallAddbackBeqQOutV5_conservation_compact
      hb3nz hq_over h_borrow h_carry2)
    h_rem_lt

/-- The compact normalized quotient target is the original unnormalized `qTrue`.

    `n4CallAddbackBeqUNormValV5` and `n4CallAddbackBeqUNormVal` are definitionally
    identical (both `val256 U0..U3 + U4.toNat * 2^256`), so the version-agnostic
    `n4CallAddbackBeqNormalized_div_eq_qTrue` applies after unfolding. -/
theorem n4CallAddbackBeqNormalized_div_eq_qTrueV5
    {a b : EvmWord}
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0) :
    n4CallAddbackBeqUNormValV5 a b / n4CallAddbackBeqBNormVal b =
      n4CallAddbackBeqQTrue a b := by
  have h := n4CallAddbackBeqNormalized_div_eq_qTrue (a := a) (b := b) hshift_nz
  simpa [n4CallAddbackBeqUNormValV5, n4CallAddbackBeqUNormVal] using h

/-- Runtime-condition semantic bridge after the normalized quotient target has
    been identified with the original unnormalized `qTrue`. -/
theorem n4CallAddbackBeqSemanticHoldsV5_of_runtime_top_nonzero
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hq_over :
      (n4CallAddbackBeqQHatV5 a b).toNat ≤
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
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b)
    (h_norm_div :
      n4CallAddbackBeqUNormValV5 a b / n4CallAddbackBeqBNormVal b =
        n4CallAddbackBeqQTrue a b) :
    n4CallAddbackBeqSemanticHoldsV5 a b := by
  show (n4CallAddbackBeqQOutV5 a b).toNat = n4CallAddbackBeqQTrue a b
  rw [n4CallAddbackBeqQOutV5_toNat_eq_normalized_div_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt]
  exact h_norm_div

/-- Runtime-condition semantic bridge after discharging the normalized-divisor
    scaling step from the CLZ shift nonzero condition.

    V5 mirror of `n4CallAddbackBeqSemanticHoldsV4_of_runtime_conditions`.  Still
    takes the trial-quotient `hq_over` bound as a hypothesis; the public
    unconditional wrapper lives in `N4SemanticGen.lean`. -/
theorem n4CallAddbackBeqSemanticHoldsV5_of_runtime_conditions_legacy
    {a b : EvmWord}
    (hb3nz : b.getLimbN 3 ≠ 0)
    (hshift_nz : (clzResult (b.getLimbN 3)).1 ≠ 0)
    (hq_over : (n4CallAddbackBeqQHatV5 a b).toNat ≤
        EvmWord.val256 (n4CallAddbackBeqU0 a b) (n4CallAddbackBeqU1 a b)
          (n4CallAddbackBeqU2 a b) (n4CallAddbackBeqU3 a b) /
        EvmWord.val256 (n4CallAddbackBeqB0Prime b) (n4CallAddbackBeqB1Prime b)
          (n4CallAddbackBeqB2Prime b) (n4CallAddbackBeqB3Prime b) + 1)
    (h_borrow : isAddbackBorrowN4CallV5Evm a b)
    (h_carry2 : isAddbackCarry2NzN4CallV5Evm a b)
    (h_rem_lt : n4CallAddbackBeqIterRNormValV5 a b < n4CallAddbackBeqBNormVal b) :
    n4CallAddbackBeqSemanticHoldsV5 a b :=
  n4CallAddbackBeqSemanticHoldsV5_of_runtime_top_nonzero
    hb3nz hq_over h_borrow h_carry2 h_rem_lt
    (n4CallAddbackBeqNormalized_div_eq_qTrueV5 hshift_nz)

end EvmWord

end EvmAsm.Evm64
