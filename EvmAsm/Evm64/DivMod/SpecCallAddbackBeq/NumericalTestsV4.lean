/-
  EvmAsm.Evm64.DivMod.SpecCallAddbackBeq.NumericalTestsV4

  Numerical validation tests for `div128Quot_v4` (the fully-corrected
  algorithm with Phase-1 AND Phase-2 2-correction). All proofs are
  `by decide`.

  Companion to `NumericalTests.lean` (v2 — kept for the historical
  bug witness on a counterexample input).
-/

import EvmAsm.Evm64.DivMod.LoopDefs.IterV4
import EvmAsm.Evm64.DivMod.SpecCallAddbackBeq

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- **div128Quot_v4 produces the correct quotient on the v2 truncation
    counterexample**: v2 undershoots by 2^32 here (per
    `div128Quot_v2_buggy_at_unreachable_uHi`); v4 produces the correct
    quotient.

    Kernel-checked via `decide`. -/
theorem div128Quot_v4_correct_at_v2_truncation_input :
    let uHi : Word := BitVec.ofNat 64 (2^64 - 2^32 + 1)
    let uLo : Word := 0
    let vTop : Word := BitVec.ofNat 64 (2^64 - 1)
    let qHat := div128Quot_v4 uHi uLo vTop
    qHat.toNat = (uHi.toNat * 2^64 + uLo.toNat) / vTop.toNat := by
  decide

/-- **div128Quot_v4 satisfies Knuth-A** on the v1 counterexample. -/
theorem div128Quot_v4_knuth_A_on_counterexample :
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
    (div128Quot_v4 u4 u3 b3').toNat ≥
      (u4.toNat * 2^32 + div_un1.toNat) /
      (dHi.toNat * 2^32 + dLo.toNat) * 2^32 := by
  decide

/-- **Layer 2a numerical validation**: on the v1 counterexample
    (a3=2^63+2^33, b3=1, b2=2^33-1), check whether the carry partition
    holds for v4. Specifically: we compute `carry` (post-mulsub addback
    carry) and `qHat` (the v4 trial digit), and verify the relationship
    against `q_true = val256(a)/val256(b)`.

    On this input, v4's `qHat = q_true + ?` and `carry = ?` (validated by
    `decide`). This data point informs whether Layer 2a-fwd's claim
    `carry = 0 ↔ qHat ≥ q_true + 2` holds for v4 under
    `isAddbackBorrowN4CallEvm_v4`. -/
theorem layer_2a_partition_holds_on_v1_counterexample :
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
    let qHat := div128Quot_v4 u4 u3 b3'
    let ms := mulsubN4 qHat b0' b1' b2' b3' u0 u1 u2 u3
    let carry := addbackN4_carry ms.1 ms.2.1 ms.2.2.1 ms.2.2.2.1 b0' b1' b2' b3'
    let q_true := val256 (a.getLimbN 0) (a.getLimbN 1) (a.getLimbN 2) (a.getLimbN 3) /
                    val256 (b.getLimbN 0) (b.getLimbN 1) (b.getLimbN 2) (b.getLimbN 3)
    -- Layer 2a forward direction: carry = 0 → qHat ≥ q_true + 2.
    -- Layer 2a backward direction: qHat ≥ q_true + 2 → carry = 0.
    (carry = 0 ↔ qHat.toNat ≥ q_true + 2) := by
  decide

end EvmAsm.Evm64
