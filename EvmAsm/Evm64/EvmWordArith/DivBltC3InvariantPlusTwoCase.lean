/-
  EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantPlusTwoCase

  BLT analog of `DivC3InvariantPlusTwoCase` — discharges
  `MulsubBltC3OneOfCarryZero` under a `+2` val256-level overestimate
  on `divKTrialCallV4QHat` plus the unreachability of `c3 ∈ {0, 2}`
  under `carry = 0`.

  Mirrors the MAX-side reduction (PR #7042) for the v4 call-trial.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantUnifiedCase
public import EvmAsm.Evm64.EvmWordArith.DivMulsubC3LeTwo

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- Frontier predicate: under the v4 call-trial, `c3 = 2` with
    first-addback carry `= 0` does not occur on the selected BLT path. -/
def MulsubBltC3UnreachableCarryZeroC3Two
    (uHi uLo vTop : Word) (v0 v1 v2 v3 u0 u1 u2 u3 : Word) : Prop :=
  ¬ (addbackN4_carry
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.2.1
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.1
        v0 v1 v2 v3 = 0 ∧
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2)

/-- `MulsubBltC3OneOfCarryZero` from a `+2` val256-level overestimate
    on the v4 trial and the unreachability of both `c3 = 0` and
    `c3 = 2` cases (under `carry = 0`). -/
theorem MulsubBltC3OneOfCarryZero_of_plus_two_and_unreach
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2) :
    MulsubBltC3UnreachableCarryZeroC3Zero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 →
    MulsubBltC3UnreachableCarryZeroC3Two uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 →
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  intro h_unreach0 h_unreach2
  show _ → _
  intro h_carry_zero
  unfold MulsubBltC3UnreachableCarryZeroC3Zero at h_unreach0
  unfold MulsubBltC3UnreachableCarryZeroC3Two at h_unreach2
  have h_c3_le_two := mulsubN4_c3_le_two hbnz hq_over
  apply BitVec.eq_of_toNat_eq
  rcases Nat.lt_or_ge
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 1
      with h_lt1 | h_ge1
  · exfalso
    have h_c3_zero :
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 := by
      apply BitVec.eq_of_toNat_eq
      have h_zero :
          (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
        omega
      rw [h_zero]; rfl
    exact h_unreach0 ⟨h_carry_zero, h_c3_zero⟩
  · rcases Nat.lt_or_ge
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 2
        with h_lt2 | h_ge2
    · have h_eq :
          (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1 := by
        omega
      rw [h_eq]; rfl
    · exfalso
      have h_c3_two_toNat :
          (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 2 := by
        omega
      exact h_unreach2 ⟨h_carry_zero, h_c3_two_toNat⟩

end EvmAsm.Evm64
