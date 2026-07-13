/-
  EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5Native

  The native v5 call-skip lower bound: the v5 trial quotient
  `divKTrialCallV5QHat u4 u3 b3'` (over the normalized n=4 top window) is an
  OVERESTIMATE of the true 256/256 quotient `val256 a / val256 b`, under the n=4
  shape (`b3 ≠ 0`), `shift ≠ 0`, and the call-trial condition `isCallTrialN4`.

  Composes:
  * `q_true_triple_bridge_to_val256_norm` — the Knuth normalized bound
    `val256 a / val256 b ≤ (u4·2^64 + u3) / b3'` (top-window quotient ≥ full
    quotient), and
  * `div128Quot_v5_ge_q_true` — the v5 trial is ≥ the exact top-window quotient
    (given `b3' ≥ 2^63` from normalization and `u4 < b3'` from `isCallTrialN4`),

  via `divKTrialCallV5QHat = div128Quot_v5`.

  This is the v5-native counterpart of `div128Quot_call_skip_ge_val256_div_v2` —
  crucially UNCONDITIONAL (no runtime no-wrap branch certificate), because the v5
  trial has a clean lower bound (`div128Quot_v5_ge_q_true`) where the v4 trial's
  lower bound required the `n4CallSkipRuntimeBranchV4` disjunction that the v4
  track never discharged from shape.  This unblocks discharging the call-skip
  semantic of the n=4 shift≠0 certificate `n4ShiftNzLaneRuntimeCertV5` from shape.
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV2
import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- The v5 call-skip trial quotient over-estimates the full 256/256 quotient
    (UNCONDITIONAL on the n=4 shape + `shift ≠ 0` + `isCallTrialN4`). -/
theorem divKTrialCallV5QHat_ge_val256_div (a0 a1 a2 a3 b0 b1 b2 b3 : Word)
    (hb3nz : b3 ≠ 0)
    (hshift_nz : (clzResult b3).1 ≠ 0)
    (hcall : isCallTrialN4 a3 b2 b3) :
    let shift := (clzResult b3).1.toNat % 64
    let antiShift := (signExtend12 (0 : BitVec 12) - (clzResult b3).1).toNat % 64
    let b3' := (b3 <<< shift) ||| (b2 >>> antiShift)
    let u4 := a3 >>> antiShift
    let u3 := (a3 <<< shift) ||| (a2 >>> antiShift)
    val256 a0 a1 a2 a3 / val256 b0 b1 b2 b3 ≤ (divKTrialCallV5QHat u4 u3 b3').toNat := by
  intro shift antiShift b3' u4 u3
  have h_bridge := q_true_triple_bridge_to_val256_norm a0 a1 a2 a3 b0 b1 b2 b3
    hshift_nz hb3nz
  simp only [] at h_bridge
  have h_b3'_ge : b3'.toNat ≥ 2 ^ 63 :=
    b3_prime_ge_pow63 b3 b2 hb3nz (signExtend12 (0 : BitVec 12) - (clzResult b3).1)
  have h_u4_lt : u4.toNat < b3'.toNat := isCallTrialN4_toNat_lt a3 b2 b3 hcall
  have h_v5_ge := div128Quot_v5_ge_q_true u4 u3 b3' h_b3'_ge h_u4_lt
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact le_trans h_bridge h_v5_ge

end EvmAsm.Evm64
