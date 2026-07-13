/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialValue

  The v5 trial-quotient value at `uHi = 0` (the shift=0 top window):
  `(divKTrialCallV5QHat 0 uLo vTop).toNat = uLo.toNat / vTop.toNat`, under the
  normalization `vTop.toNat ≥ 2^63`.  On the shift=0 branch the n=4 divisor top
  limb `b3 = vTop` already has its top bit set, and the dividend top window is
  `(uHi, uLo) = (0, a3)`, so the trial quotient is exactly the top-limb quotient
  `a3 / b3`.  This is the lower-bound input for the n=4 shift=0 skip word equality
  (mirroring how the v4 shift=0 proof `n4_shift0_call_skip_div_mod_getLimbN` uses
  `div128Quot_shift0_ge_a3_div_b3`).  Composes `divKTrialCallV5QHat_eq_div128Quot_v5`
  (unconditional) with `div128Quot_v5_eq_q_true` (at `uHi = 0 < vTop`).
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 trial quotient at `uHi = 0` equals the top-limb quotient `uLo / vTop`
    (as `Nat`), for a normalized `vTop ≥ 2^63`. -/
theorem divKTrialCallV5QHat_uHi_zero_toNat (uLo vTop : Word)
    (hvtop : vTop.toNat ≥ 2 ^ 63) :
    (divKTrialCallV5QHat (0 : Word) uLo vTop).toNat = uLo.toNat / vTop.toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  have hlt : (0 : Word).toNat < vTop.toNat := by
    have : (0 : Word).toNat = 0 := rfl
    omega
  rw [div128Quot_v5_eq_q_true (0 : Word) uLo vTop hvtop hlt]
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0]
  simp

end EvmAsm.Evm64
