/-
  EvmAsm.Evm64.EvmWordArith.DivKnuthAEqualWindow

  Trivial discharge of `Knuth128_64TopWindowLeVal256DivPlusOne` under the
  "equal-window" condition: when `val256(u) = uHi * 2^64 + uLo` and
  `val256(v) = vTop` (i.e., the val256-level quotient is exactly the
  128/64 quotient), the +1 bound holds with equality.

  This handles the simplest case of the val256-level Knuth Theorem A
  bridge — when the window IS the full value.  The general case (the
  open frontier `Knuth128_64TopWindowLeVal256DivPlusOne`) handles
  non-trivial dividend tails and divisor tails.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivV4TrialVal256Composition

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Discharge `Knuth128_64TopWindowLeVal256DivPlusOne` when the val256
    values match the 128/64 window exactly. -/
theorem Knuth128_64TopWindowLeVal256DivPlusOne_of_eq_window
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_v_eq : val256 v0 v1 v2 v3 = vTop.toNat)
    (h_u_eq : val256 u0 u1 u2 u3 = uHi.toNat * 2^64 + uLo.toNat) :
    Knuth128_64TopWindowLeVal256DivPlusOne uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold Knuth128_64TopWindowLeVal256DivPlusOne
  rw [h_v_eq, h_u_eq]
  -- Goal: x / vTop ≤ x / vTop + 1
  omega

end EvmAsm.Evm64
