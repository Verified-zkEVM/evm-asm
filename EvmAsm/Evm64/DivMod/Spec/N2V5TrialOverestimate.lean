/-
  EvmAsm.Evm64.DivMod.Spec.N2V5TrialOverestimate

  The v5 n=2 trial +2 overestimate (call regime), abstract over the per-digit
  `u`-window: `divKTrialCallV5QHat u2 u1 v1 ≤ val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2`.

  This is the call-digit hypothesis (`hq_over`) that
  `callAddbackCarry2NzV5_of_overestimate_c3` (#7424) consumes.  Built by
  composing `div128Quot_v5_le_q_true` (the EXACT single-limb floor bound, valid
  in the CALL regime `u2 < v1` — NOT `_le_q_true_plus_one`, which would give +3)
  with `knuth_theorem_b_abstract`, applying the latter to the `2^128`-scaled
  window so its `2^256/2^192` split matches the n=2 2-limb divisor and
  `Nat.mul_div_mul_left` collapses the scale.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD
import EvmAsm.Evm64.EvmWordArith.KnuthTheoremB

namespace EvmAsm.Evm64

open EvmAsm.Rv64
open EvmWord (val256)

/-- v5 n=2 call-digit +2 overestimate, abstract over the digit's `u`-window
    `(u0, u1, u2)` and the (already normalized) 2-limb divisor `(v0, v1)`. -/
theorem divKTrialCallV5QHat_le_window_div_plus_two_of_call
    (u0 u1 u2 v0 v1 : Word)
    (hv1_norm : v1.toNat ≥ 2 ^ 63)
    (hcall : u2.toNat < v1.toNat) :
    (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 0 / val256 v0 v1 0 0 + 2 := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  have h1 := div128Quot_v5_le_q_true u2 u1 v1 hv1_norm hcall
  have hvrest : v0.toNat * 2 ^ 128 < 2 ^ 192 := by
    have h := v0.isLt
    have he : (2 : Nat) ^ 192 = 2 ^ 64 * 2 ^ 128 := by norm_num
    rw [he]
    exact Nat.mul_lt_mul_of_pos_right h (by positivity)
  have h2 := knuth_theorem_b_abstract
    (2 ^ 128 * val256 u0 u1 u2 0) (2 ^ 128 * val256 v0 v1 0 0)
    u2.toNat u1.toNat (u0.toNat * 2 ^ 128)
    v1.toNat (v0.toNat * 2 ^ 128)
    (by simp only [val256]; rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]; ring)
    (by simp only [val256]; rw [show BitVec.toNat (0 : BitVec 64) = 0 from rfl]; ring)
    hvrest hv1_norm hcall u1.isLt
  rw [Nat.mul_div_mul_left _ _ (by positivity : 0 < 2 ^ 128)] at h2
  omega

end EvmAsm.Evm64
