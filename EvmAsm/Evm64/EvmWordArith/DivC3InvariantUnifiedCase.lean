/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantUnifiedCase

  Unified discharges of `MulsubMaxC3OneOfCarryZero` and
  `MulsubBltC3OneOfCarryZero` by case-splitting on the value of the
  mulsub carry `c3` (∈ {0, 1, 2, ...}) and the first-addback carry.

  Combines the `_of_c3_eq_one` trivials (PR #7036) and `_of_carry_ne_zero`
  vacuous discharges (PR #7037) into a single named entry point that
  reduces each named invariant to the SINGLE remaining frontier:
  `(first-addback carry = 0 AND c3 = 0)` — the Knuth-B unreachability case.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Unified case-discharge of `MulsubMaxC3OneOfCarryZero` from a proof
    that the `(carry = 0 ∧ c3 = 0)` case is unreachable.

    The named frontier predicate `MulsubMaxC3UnreachableCarryZeroC3Zero`
    captures exactly the substantive Knuth-B obligation: under the
    selected path, the combination `first-addback carry = 0 ∧
    mulsubN4 c3 = 0` does not occur. -/
def MulsubMaxC3UnreachableCarryZeroC3Zero (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  ¬ (addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 ∧
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0)

/-- `MulsubMaxC3OneOfCarryZero` from the unreachability of the
    `(carry = 0 ∧ c3 = 0)` case.

    With the predicate's hypothesis (carry = 0), the carry must not be
    nonzero, so the unreachability gives `c3 ≠ 0`.  And c3 is bounded by 1
    for the saturated trial (since 2^64-1 × anything < 2^65), so c3 = 1. -/
theorem MulsubMaxC3OneOfCarryZero_of_unreachable_carry0_c30
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_unreach : MulsubMaxC3UnreachableCarryZeroC3Zero v0 v1 v2 v3 u0 u1 u2 u3)
    (h_c3_le_one :
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ 1) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold MulsubMaxC3OneOfCarryZero
  intro h_carry_zero
  unfold MulsubMaxC3UnreachableCarryZeroC3Zero at h_unreach
  -- h_unreach is the negation of (carry = 0 ∧ c3 = 0).
  -- Given h_carry_zero (carry = 0), we need c3 ≠ 0.
  by_contra h_c3_ne_one
  -- We have c3 ≤ 1 and c3 ≠ 1, so c3 = 0.
  have h_c3_zero : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h_lt : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat < 1 := by
      rcases Nat.lt_or_ge
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 1 with h | h
      · exact h
      · exfalso
        apply h_c3_ne_one
        apply BitVec.eq_of_toNat_eq
        have h_eq : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1 := by
          omega
        rw [h_eq]; rfl
    have : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
      omega
    rw [this]; rfl
  exact h_unreach ⟨h_carry_zero, h_c3_zero⟩

end EvmAsm.Evm64
