/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantFromCarryNz

  Vacuous discharges of `MulsubMaxC3OneOfCarryZero` and
  `MulsubBltC3OneOfCarryZero` under the hypothesis that the first addback
  carry is nonzero.

  These are the OTHER half of the case-split (vs the `_of_c3_eq_one`
  trivials in `DivC3InvariantTrivials`): with the implication's hypothesis
  false, the predicate is vacuously true.  Together the two pairs cover
  the (carry = 0 ∨ carry ≠ 0) disjoint cases, but the carry = 0 + c3 = 0
  case still requires the genuine Knuth-B argument — that's the only
  remaining substantive frontier.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Vacuous discharge of `MulsubMaxC3OneOfCarryZero` from
    `first-addback carry ≠ 0`. -/
theorem MulsubMaxC3OneOfCarryZero_of_carry_ne_zero
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hcarry :
      addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 ≠ 0) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold MulsubMaxC3OneOfCarryZero
  intro h_eq
  exact absurd h_eq hcarry

/-- Vacuous discharge of `MulsubBltC3OneOfCarryZero` from
    `first-addback carry ≠ 0`. -/
theorem MulsubBltC3OneOfCarryZero_of_carry_ne_zero
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hcarry :
      addbackN4_carry
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 ≠ 0) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  show _ → _
  intro h_eq
  exact absurd h_eq hcarry

end EvmAsm.Evm64
