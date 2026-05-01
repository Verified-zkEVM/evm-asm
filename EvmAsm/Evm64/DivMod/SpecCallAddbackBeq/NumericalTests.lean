/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.NumericalTests

  Numerical sanity-check tests on the v2 stubs and predicates from
  `SpecCallAddbackBeq.lean`. These DO NOT prove the stubs but verify
  the statements are at least consistent on concrete witnesses,
  including the input that breaks v1. All proofs are `by decide`.

  Extracted from `SpecCallAddbackBeq.lean` (2026-04-28) to ease the
  file-size guardrail.
-/

import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

-- ============================================================================
-- Numerical sanity checks on the v2 stubs (counterexample + variants).
-- These do NOT prove the stubs but verify the statements are at least
-- consistent on concrete witnesses, including the input that breaks v1.
-- ============================================================================

/-- **Sanity check 1**: `div128Quot_v2_le_val256_div_plus_two`'s bound holds
    on the counterexample input (the same (a, b) where v1's `div128Quot`
    overshoots by 2^32-2). Kernel-checked via `decide`. -/
theorem div128Quot_v2_le_val256_div_plus_two_test_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  decide

/-- **Sanity check 2**: by contrast, the buggy v1 `div128Quot` VIOLATES
    the same bound on the same input (overshoots by 2^32-2 ≫ 2). This
    is the underlying motivation for the v2 fix. Kernel-checked via `decide`. -/
theorem div128Quot_v1_violates_knuth_B_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    ¬ ((div128Quot u4 un3 b3').toNat ≤
        val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
          val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2) := by
  decide

/-- **Sanity check 3**: `div128Quot_v2_le_val256_div_plus_two` bound holds
    on a "small" test input where both v1 and v2 should agree. Verifies
    the bound isn't trivially false on common cases. Kernel-checked via `decide`. -/
theorem div128Quot_v2_le_val256_div_plus_two_test_small :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 5 | 3 => BitVec.ofNat 64 (2^60))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^32 + 7))
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let u4 := (a.getLimbN 3) >>> antiShift
    let un3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 un3 b3').toNat ≤
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) + 2 := by
  decide

/-- **Sanity check 5**: `addback_carry_partition_v2`'s claim on the
    counterexample input. v2 returns `qHat = q_true + 1` on this input
    (per `n4CallAddbackBeqSemanticHolds_v2_holds_on_counterexample`), so
    the partition's claim is: `carry ≠ 0` (single-addback case).

    Kernel-checked validation that the partition's stated form is at
    least correct on the canonical counterexample. -/
theorem addback_carry_partition_v2_test_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0 := by
  decide

/-- **Sanity check 11**: on the v1 counterexample, the clean shifted-domain
    lower bound `q_true_shifted + 1 ≤ qHat.toNat` (conclusion of
    `qHat_lower_shifted_under_runtime_v2`) holds. Kernel-checked via
    `decide`. -/
theorem qHat_lower_shifted_v2_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' + 1 ≤ qHat.toNat := by
  decide

/-- **Sanity check 10**: on the v1 counterexample, the shifted-domain
    divisor inequality `qHat > val256(a_shifted) / val256(b_shifted)`
    (the conclusion of `qHat_gt_q_true_shifted_under_runtime_v2`)
    holds. Kernel-checked via `decide`.

    This complements check 8 (the multiplicative form). -/
theorem qHat_gt_q_true_shifted_v2_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat > val256 u0 u1 u2 u3 / val256 b0' b1' b2' b3' := by
  decide

/-- **Sanity check 8**: on the v1 counterexample, the shifted-domain
    inequality `qHat * val256(b_shifted) > val256(a_shifted)` (the
    conclusion of `qHat_mul_b_shifted_gt_a_shifted_under_runtime_v2`)
    holds. Kernel-checked via `decide`. -/
theorem qHat_mul_b_shifted_gt_a_shifted_v2_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    qHat.toNat * val256 b0' b1' b2' b3' > val256 u0 u1 u2 u3 := by
  decide

/-- **Sanity check 7**: on the v1 counterexample input, qHat (v2) > q_true
    holds — i.e., the conclusion of `qHat_gt_q_true_under_runtime_v2`
    is verified on this concrete witness (kernel-checked via `decide`).

    Concretely: q_true = 9223372041149743102, v2 qHat = q_true + 1 =
    9223372041149743103. So qHat > q_true. ✓

    This bounds the lemma claim: it's at least correct on the worst-known
    case (the v1 counterexample). -/
theorem qHat_gt_q_true_v2_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    (div128Quot_v2 u4 u3 b3').toNat >
      val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
        val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3) := by
  decide

/-- **Sanity check 6**: on the v1 counterexample input, both v1 and v2
    borrow predicates fire (kernel-checked via `decide`).

    This is preliminary evidence that on this specific input, the v1
    and v2 borrow predicates agree. A full equivalence theorem would be
    needed to use v1's `hborrow` lemmas in the v2 closure proof — this
    test just suggests it's not refuted on the worst-known case. -/
theorem isAddbackBorrowN4Call_v1_v2_agree_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    isAddbackBorrowN4CallEvm a b ↔ isAddbackBorrowN4CallEvm_v2 a b := by
  unfold isAddbackBorrowN4CallEvm isAddbackBorrowN4CallEvm_v2
         isAddbackBorrowN4Call isAddbackBorrowN4Call_v2
  decide

/-- **Sanity check 9**: v1/v2 borrow agreement on a SECOND input —
    a "small" case where both v1 and v2 algorithms compute the same
    qHat (no overshoot beyond +2). Kernel-checked via `decide`.

    Together with `isAddbackBorrowN4Call_v1_v2_agree_on_counterexample`
    (the worst-known case), this gives evidence that v1 ↔ v2 borrow
    equivalence holds broadly. A general theorem would unblock using
    v1's lemmas (like `u_top_lt_c3_of_addback_borrow_call`) directly
    in v2 closure proofs. -/
theorem isAddbackBorrowN4Call_v1_v2_agree_on_small :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 5 | 3 => BitVec.ofNat 64 (2^60))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^32 + 7))
    isAddbackBorrowN4CallEvm a b ↔ isAddbackBorrowN4CallEvm_v2 a b := by
  unfold isAddbackBorrowN4CallEvm isAddbackBorrowN4CallEvm_v2
         isAddbackBorrowN4Call isAddbackBorrowN4Call_v2
  decide

/-- **Numerical validation of `addback_carry_partition_v2_nonzero_case`.**
    On the v1 counterexample, carry ≠ 0 (single-addback case fires) and
    the conclusion `qHat = q_true + 1` holds. Kernel-checked via `decide`.
    Confirms the case lemma's claim is at least correct on this witness. -/
theorem addback_carry_partition_v2_nonzero_case_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' ≠ 0 →
    qHat.toNat = q_true + 1 := by
  decide

/-- **Numerical validation of `addback_carry_partition_v2_zero_case`.**
    On the v1 counterexample, carry ≠ 0, so the implication
    `carry = 0 → qHat = q_true + 2` is vacuously true. Kernel-checked
    via `decide`. Confirms the case lemma's stated form is at least
    well-typed; doesn't witness the conclusion since the antecedent fails.

    A non-vacuous validation would require an input where carry = 0 actually
    fires (double-addback). Such inputs are rarer; the counterexample is
    designed to test single-addback specifically. -/
theorem addback_carry_partition_v2_zero_case_on_counterexample :
    let a : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => 0 | 3 => BitVec.ofNat 64 (2^63 + 2^33))
    let b : EvmWord := EvmWord.fromLimbs (fun i => match i with
      | 0 => 0 | 1 => 0 | 2 => BitVec.ofNat 64 (2^33 - 1) | 3 => 1)
    let shift := (clzResult (b.getLimbN 3)).1.toNat % 64
    let antiShift :=
      (signExtend12 (0 : BitVec 12) - (clzResult (b.getLimbN 3)).1).toNat % 64
    let b3' := ((b.getLimbN 3) <<< shift) ||| ((b.getLimbN 2) >>> antiShift)
    let b2' := ((b.getLimbN 2) <<< shift) ||| ((b.getLimbN 1) >>> antiShift)
    let b1' := ((b.getLimbN 1) <<< shift) ||| ((b.getLimbN 0) >>> antiShift)
    let b0' := (b.getLimbN 0) <<< shift
    let u4 := (a.getLimbN 3) >>> antiShift
    let u3 := ((a.getLimbN 3) <<< shift) ||| ((a.getLimbN 2) >>> antiShift)
    let u2 := ((a.getLimbN 2) <<< shift) ||| ((a.getLimbN 1) >>> antiShift)
    let u1 := ((a.getLimbN 1) <<< shift) ||| ((a.getLimbN 0) >>> antiShift)
    let u0 := (a.getLimbN 0) <<< shift
    let qHat := div128Quot_v2 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                  val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3' = 0 →
    qHat.toNat = q_true + 2 := by
  decide

/-- **Numerical validation of `div128Quot_v2_knuth_A_under_runtime`.**
    On the v1 counterexample, the Knuth-A v2 lower bound
    `q1'' ≥ floor(x / vTop)` (where x = u4*2^32 + div_un1, vTop = dHi*2^32 + dLo)
    holds. Kernel-checked via `decide`. -/
theorem div128Quot_v2_knuth_A_v2_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    q1''.toNat ≥ (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat) := by
  decide

/-- **Numerical validation of `div128Quot_v2_phase2_no_wrap_lo_under_runtime`.**
    On the v1 counterexample, the Phase-2 lower bound
    `q0' * dLo ≤ rhat2' * 2^32 + div_un0` holds. Kernel-checked via `decide`.
    The Phase-2 mirror of `div128Quot_v2_phase1_no_wrap_lo_untruncated_HOLDS_on_counterexample`. -/
theorem div128Quot_v2_phase2_no_wrap_lo_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let div_un0 := (u3 <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let q1' := if BitVec.ult rhatUn1 qDlo then q1c + signExtend12 4095 else q1c
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q1'' := div128Quot_phase2b_q0' q1' rhat' dLo div_un1
    let rhat'' :=
      if rhat' >>> (32 : BitVec 6).toNat = 0 then
        let qDlo2 := q1' * dLo
        let rhatUn1' := (rhat' <<< (32 : BitVec 6).toNat) ||| div_un1
        if BitVec.ult rhatUn1' qDlo2 then rhat' + dHi else rhat'
      else rhat'
    let cu_rhat_un1 := (rhat'' <<< (32 : BitVec 6).toNat) ||| div_un1
    let cu_q1_dlo := q1'' * dLo
    let un21 := cu_rhat_un1 - cu_q1_dlo
    let q0 := rv64_divu un21 dHi
    let rhat2 := un21 - q0 * dHi
    let hi2 := q0 >>> (32 : BitVec 6).toNat
    let q0c := if hi2 = 0 then q0 else q0 + signExtend12 4095
    let rhat2c := if hi2 = 0 then rhat2 else rhat2 + dHi
    let q0' := div128Quot_phase2b_q0' q0c rhat2c dLo div_un0
    let rhat2' := if rhat2c >>> (32 : BitVec 6).toNat = 0 then
                    (if BitVec.ult ((rhat2c <<< (32 : BitVec 6).toNat) ||| div_un0)
                                    (q0c * dLo) then rhat2c + dHi else rhat2c)
                  else rhat2c
    q0'.toNat * dLo.toNat ≤ rhat2'.toNat * 2^32 + div_un0.toNat := by
  decide

/-- **Numerical validation of `div128Quot_v2_phase1c_in_knuth_range_under_runtime`** (Stub 1):
    on the v1 counterexample, q* ≤ q1c ≤ q* + 2 (Knuth's TAOCP A+B at the
    initial trial level). Kernel-checked via `decide`. -/
theorem div128Quot_v2_phase1c_in_knuth_range_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let q_true := (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat)
    q_true ≤ q1c.toNat ∧ q1c.toNat ≤ q_true + 2 := by
  decide

/-- **Numerical validation of `div128Quot_v2_phase1b_2nd_guard_under_runtime`** (Stub 3):
    on the v1 counterexample, the conditional implication
    `q1c_overshoot_2 → rhat' < 2^32` holds. Kernel-checked via `decide`.

    NOTE: this validation may be vacuous if q1c doesn't overshoot by 2 on
    this specific input. The decide-check still exercises the conditional
    structure and catches errors in the statement form. -/
theorem div128Quot_v2_phase1b_2nd_guard_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b2 : Word := BitVec.ofNat 64 (2^33 - 1)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let b3' := (b3 <<< (shift.toNat % 64)) ||| (b2 >>> (antiShift.toNat % 64))
    let u4 := a3 >>> (antiShift.toNat % 64)
    let u3 := (a3 <<< (shift.toNat % 64)) ||| ((0:Word) >>> (antiShift.toNat % 64))
    let dHi := b3' >>> (32 : BitVec 6).toNat
    let dLo := (b3' <<< (32 : BitVec 6).toNat) >>> (32 : BitVec 6).toNat
    let div_un1 := u3 >>> (32 : BitVec 6).toNat
    let q1 := rv64_divu u4 dHi
    let rhat := u4 - q1 * dHi
    let hi1 := q1 >>> (32 : BitVec 6).toNat
    let q1c := if hi1 = 0 then q1 else q1 + signExtend12 4095
    let rhatc := if hi1 = 0 then rhat else rhat + dHi
    let qDlo := q1c * dLo
    let rhatUn1 := (rhatc <<< (32 : BitVec 6).toNat) ||| div_un1
    let rhat' := if BitVec.ult rhatUn1 qDlo then rhatc + dHi else rhatc
    let q_true := (u4.toNat * 2^32 + div_un1.toNat) / (dHi.toNat * 2^32 + dLo.toNat)
    q1c.toNat = q_true + 2 → rhat'.toNat < 2^32 := by
  decide

/-- **Algorithm-level bug at unreachable input** (numerical validation 2026-04-28):
    `div128Quot_v2 (2^64-2^32+1) 0 (2^64-1)` undershoots the true quotient
    by exactly `2^32`, demonstrating the `(uHi, uLo, vTop)`-level vulnerability
    of the Phase-1 truncation regime (sub-case 0b: hi1 ≠ 0, rhatc ≥ 2^32,
    1st BLTU spuriously fires + Phase-2b guard skips correction).

    However: this input has `uHi = 2^64-2^32+1 > 2^63`, which is unreachable
    from valid `(a, b)` inputs after shift normalization. The pipeline gives
    `u4 = a3 >>> antiShift` with `antiShift ∈ [1, 63]` (under `_hshift_nz`),
    so `u4 < 2^shift ≤ 2^63`.

    True quotient: `((2^64-2^32+1) * 2^64) / (2^64-1) = 2^64-2^32+1`.
    Algorithm output: `2^64-2^33+1` (undershoot = 2^33 - 2^32 = 2^32).

    See `div128Quot_v4` (in `LoopDefs/IterV4.lean`) for the FIXED algorithm
    with the `rhatc >> 32 = 0` guard on the 1st correction (and full
    2-correction in both phases). -/
theorem div128Quot_v2_buggy_at_unreachable_uHi :
    let uHi : Word := BitVec.ofNat 64 (2^64 - 2^32 + 1)
    let uLo : Word := 0
    let vTop : Word := BitVec.ofNat 64 (2^64 - 1)
    let qHat := div128Quot_v2 uHi uLo vTop
    -- Algorithm undershoots by exactly 2^32.
    qHat.toNat = 2^64 - 2^33 + 1 ∧
    qHat.toNat + 2^32 =
      (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  decide

/-- **v1 lower-bound failure at the same unreachable wide-uHi input.**
    This refutes the all-regime lemma shape
    `uHi < vTop -> q_true <= div128Quot uHi uLo vTop` for the current v1
    `div128Quot`. The missing runtime fact is `uHi < 2^63`; without it,
    the unguarded first D3 correction can undershoot. -/
theorem div128Quot_v1_lower_bound_false_at_unreachable_uHi :
    let uHi : Word := BitVec.ofNat 64 (2^64 - 2^32 + 1)
    let uLo : Word := 0
    let vTop : Word := BitVec.ofNat 64 (2^64 - 1)
    vTop.toNat ≥ 2^63 ∧
    uHi.toNat < vTop.toNat ∧
    ¬ ((uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat ≤
        (div128Quot uHi uLo vTop).toNat) := by
  decide

/-- **u4 bound under runtime preconditions** (numerical evidence):
    On the v1 counterexample, `u4 < 2^63`, confirming the case 0 closure
    plan. Together with `dHi ≥ 2^31`, this gives `q1 < 2^32`, hence
    `hi1 = 0`, hence `rhatc < dHi < 2^32`. So the truncation regime
    sub-case 0b never arises. -/
theorem u4_lt_pow63_on_counterexample :
    let a3 : Word := BitVec.ofNat 64 (2^63 + 2^33)
    let b3 : Word := 1
    let shift := (clzResult b3).1
    let antiShift := signExtend12 (0 : BitVec 12) - shift
    let u4 := a3 >>> (antiShift.toNat % 64)
    u4.toNat < 2^63 := by
  decide

-- **Sanity check 4**: NOTE — `n4CallAddbackBeqSemanticHolds_v2` requires
-- the input to actually be in the call+addback BEQ runtime regime (i.e.
-- the runtime preconditions of the closure stub: `hbltu`, `hcarry2_nz`,
-- `hborrow`). On arbitrary inputs the predicate doesn't hold — the closure
-- only asserts conditional correctness. The counterexample
-- (`...holds_on_counterexample` above) was specifically constructed to be
-- in the BEQ regime, which is why it's the right witness.

end EvmAsm.Evm64
