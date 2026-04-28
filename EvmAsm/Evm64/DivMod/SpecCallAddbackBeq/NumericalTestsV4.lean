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

end EvmAsm.Evm64
