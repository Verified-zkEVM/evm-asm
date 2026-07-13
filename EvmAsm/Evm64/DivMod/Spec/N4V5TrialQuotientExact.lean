/-
  EvmAsm.Evm64.DivMod.Spec.N4V5TrialQuotientExact

  The v5 trial quotient is the exact window floor: under the call regime
  (normalised divisor `vTop ≥ 2^63`) and the trial precondition `uHi < vTop`,
  `divKTrialCallV5QHat uHi uLo vTop = floor((uHi·2^64 + uLo) / vTop)`.  Composes
  the proven `divKTrialCallV5QHat_eq_div128Quot_v5` (the v5 trial folds to the v5
  capped Knuth-D 128/64 quotient) with `div128Quot_v5_eq_q_true` (that capped
  quotient is exact in this regime).  This is the trial→arithmetic step of the
  n=4 v5 quotient-word equality (`fullDivN4QuotientWordV5 … = EvmWord.div a b`):
  it pins the code's trial quotient to the normalised-window division, leaving
  only the shift-normalisation invariance (window quotient = a / b) to the lane.
  Bead `evm-asm-wbc4i.8`.
-/

import EvmAsm.Evm64.EvmWordArith.CallSkipLowerBoundV5.V5BoundChainD

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- The v5 trial quotient equals the exact floor of the 128/64 window division,
    in the call regime (`vTop ≥ 2^63`, `uHi < vTop`). -/
theorem divKTrialCallV5QHat_eq_qTrue (uHi uLo vTop : Word)
    (hvTop_ge : vTop.toNat ≥ 2 ^ 63)
    (huHi_lt_vTop : uHi.toNat < vTop.toNat) :
    (divKTrialCallV5QHat uHi uLo vTop).toNat =
      (uHi.toNat * 2 ^ 64 + uLo.toNat) / vTop.toNat := by
  rw [divKTrialCallV5QHat_eq_div128Quot_v5]
  exact div128Quot_v5_eq_q_true uHi uLo vTop hvTop_ge huHi_lt_vTop

end EvmAsm.Evm64
