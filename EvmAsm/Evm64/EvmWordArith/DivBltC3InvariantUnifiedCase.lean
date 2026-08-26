/-
  EvmAsm.Evm64.EvmWordArith.DivBltC3InvariantUnifiedCase

  BLT analog of `DivC3InvariantUnifiedCase` — names the
  `MulsubBltC3UnreachableCarryZeroC3Zero` frontier predicate and discharges
  `MulsubBltC3OneOfCarryZero` from it plus `c3 ≤ 1`.

  Mirrors the MAX-side reduction (PR #7038) for the v4 call-trial
  `divKTrialCallV4QHat`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- BLT-side Knuth-B unreachability frontier: the combination
    `first-addback carry = 0 ∧ mulsub c3 = 0` does not occur on the
    selected BLT path.  Parametrised on the v4 trial input
    `(uHi, uLo, vTop)`. -/
def MulsubBltC3UnreachableCarryZeroC3Zero
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
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0)

/-- BLT analog of `MulsubMaxC3OneOfCarryZero_of_unreachable_carry0_c30`. -/
theorem MulsubBltC3OneOfCarryZero_of_unreachable_carry0_c30
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 : Word)
    (h_unreach : MulsubBltC3UnreachableCarryZeroC3Zero uHi uLo vTop
      v0 v1 v2 v3 u0 u1 u2 u3)
    (h_c3_le_one :
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≤ 1) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  show _ → _
  intro h_carry_zero
  unfold MulsubBltC3UnreachableCarryZeroC3Zero at h_unreach
  by_contra h_c3_ne_one
  have h_c3_zero :
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 0 := by
    apply BitVec.eq_of_toNat_eq
    have h_lt : (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat < 1 := by
      rcases Nat.lt_or_ge
        (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
          v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat 1 with h | h
      · exact h
      · exfalso
        apply h_c3_ne_one
        apply BitVec.eq_of_toNat_eq
        have h_eq : (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
            v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1 := by
          omega
        rw [h_eq]; rfl
    have : (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop)
        v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 0 := by
      omega
    rw [this]; rfl
  exact h_unreach ⟨h_carry_zero, h_c3_zero⟩

end EvmAsm.Evm64
