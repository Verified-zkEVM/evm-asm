/-
  EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialBounds

  The v5 trial-quotient bound at `uHi = 0` (the shift=0 top window):
  `(divKTrialCallV5QHat 0 uLo vTop).toNat ≤ 1`, under the normalization
  `vTop.toNat ≥ 2^63`.  Since the trial equals `uLo / vTop` (by
  `divKTrialCallV5QHat_uHi_zero_toNat`, #7629) and `uLo < 2^64 ≤ 2·vTop`, the
  single-digit shift=0 quotient is at most 1.  v5 analog of the v4
  `div128Quot_shift0_le_one`; the upper bound needed by the n=4 shift=0 call+addback
  word equality (the addback corrects a trial that overestimates by 1).
  Bead `evm-asm-wbc4i.8`.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N4V5Shift0TrialValue

public section

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 trial quotient at `uHi = 0` is at most 1, for a normalized
    `vTop ≥ 2^63`. -/
theorem divKTrialCallV5QHat_uHi_zero_le_one (uLo vTop : Word)
    (hvtop : vTop.toNat ≥ 2 ^ 63) :
    (divKTrialCallV5QHat (0 : Word) uLo vTop).toNat ≤ 1 := by
  rw [divKTrialCallV5QHat_uHi_zero_toNat uLo vTop hvtop]
  have hb_pos : 0 < vTop.toNat := by omega
  have hlt : uLo.toNat / vTop.toNat < 2 := by
    rw [Nat.div_lt_iff_lt_mul hb_pos]
    have := uLo.isLt
    omega
  omega

end EvmAsm.Evm64
