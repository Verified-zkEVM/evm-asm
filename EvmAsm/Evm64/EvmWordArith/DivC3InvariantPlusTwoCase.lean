/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantPlusTwoCase

  Discharges `MulsubMaxC3OneOfCarryZero` under a `+2` val256-level
  overestimate (the natural shape-specific form from
  `max_trial_local_overestimate_n{2,3}_of_not_ult`) given two named
  unreachability frontiers:
    1. `MulsubMaxC3UnreachableCarryZeroC3Zero`: (carry = 0 ∧ c3 = 0)
       does not occur on the selected path,
    2. `MulsubMaxC3UnreachableCarryZeroC3Two`: (carry = 0 ∧ c3 = 2)
       does not occur on the selected path.

  Together with `mulsubN4_c3_le_two`, this reduces the MAX-side c3
  invariant under `+2` to exactly two sharp reachability obligations.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo
public import EvmAsm.Evm64.EvmWordArith.DivC3InvariantUnifiedCase

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Frontier predicate: under the saturated MAX trial, `c3 = 2` with
    first-addback carry `= 0` does not occur on the selected path.

    Companion to `MulsubMaxC3UnreachableCarryZeroC3Zero` for the `+2`
    case. -/
def MulsubMaxC3UnreachableCarryZeroC3Two (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  ¬ (addbackN4_carry
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 ∧
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2)

/-- `MulsubMaxC3OneOfCarryZero` from a `+2` val256-level overestimate
    and the unreachability of both `c3 = 0` and `c3 = 2` cases
    (under `carry = 0`). -/
theorem MulsubMaxC3OneOfCarryZero_of_plus_two_and_unreach
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2) :
    MulsubMaxC3UnreachableCarryZeroC3Zero v0 v1 v2 v3 u0 u1 u2 u3 →
    MulsubMaxC3UnreachableCarryZeroC3Two v0 v1 v2 v3 u0 u1 u2 u3 →
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 := by
  intro h_unreach0 h_unreach2
  unfold MulsubMaxC3OneOfCarryZero
  intro h_carry_zero
  unfold MulsubMaxC3UnreachableCarryZeroC3Zero at h_unreach0
  unfold MulsubMaxC3UnreachableCarryZeroC3Two at h_unreach2
  have h_c3_le_two := mulsubN4_c3_le_two hbnz hq_over
  -- c3 ∈ {0, 1, 2}.  Under carry = 0:
  --   c3 = 0 → contradicts h_unreach0
  --   c3 = 2 → contradicts h_unreach2 (after .toNat = 2)
  --   c3 = 1 → conclusion holds.
  apply BitVec.eq_of_toNat_eq
  rcases Nat.lt_or_ge
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 1
      with h_lt1 | h_ge1
  · -- c3 < 1, so c3 = 0 → unreachable
    exfalso
    have h_c3_zero :
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 := by
      apply BitVec.eq_of_toNat_eq
      have h_zero :
          (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
        omega
      rw [h_zero]; rfl
    exact h_unreach0 ⟨h_carry_zero, h_c3_zero⟩
  · -- c3 ≥ 1.  Then c3 ∈ {1, 2}.
    rcases Nat.lt_or_ge
        (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 2
        with h_lt2 | h_ge2
    · -- c3 = 1
      have h_eq : (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1 := by
        omega
      rw [h_eq]; rfl
    · -- c3 = 2 → unreachable
      exfalso
      have h_c3_two_toNat :
          (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2 := by
        omega
      exact h_unreach2 ⟨h_carry_zero, h_c3_two_toNat⟩

end EvmAsm.Evm64
