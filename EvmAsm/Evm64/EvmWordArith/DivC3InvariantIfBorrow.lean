/-
  EvmAsm.Evm64.EvmWordArith.DivC3InvariantIfBorrow

  IfBorrow-style discharges of `MulsubMaxC3OneOfCarryZero` and
  `MulsubBltC3OneOfCarryZero` from the algorithm's borrow check.

  The DIV loop dispatches between skip and addback paths via a borrow
  check `BitVec.ult uTop c3`.  When this check fires (addback path
  selected), the iteration is at a state where `uTop < c3`, which means
  `c3 ≠ 0` (since the smallest `uTop` is 0).  Composed with the
  Knuth-B `c3 ≤ 1` bound (from `+1` overestimate), this gives `c3 = 1`
  directly — discharging the implication's conclusion regardless of the
  first-addback carry.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivMaxC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivBltC3Invariant
public import EvmAsm.Evm64.EvmWordArith.DivN4Overestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `MulsubMaxC3OneOfCarryZero` under the addback-path selection
    (`uTop < c3`).  When the borrow check fires, `c3 ≠ 0`; with the
    `+1` overestimate giving `c3 ≤ 1`, we conclude `c3 = 1`, so the
    implication's conclusion holds unconditionally. -/
theorem MulsubMaxC3OneOfCarryZero_of_borrow_and_plus_one
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (signExtend12 (4095 : BitVec 12) : Word).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1)
    (hborrow : BitVec.ult uTop
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    MulsubMaxC3OneOfCarryZero v0 v1 v2 v3 u0 u1 u2 u3 := by
  unfold MulsubMaxC3OneOfCarryZero
  intro _
  -- uTop < c3 ⟹ c3 ≠ 0.
  have h_c3_nz :
      (mulsubN4 (signExtend12 4095) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 ≠ 0 := by
    intro h0
    rw [h0] at hborrow
    -- uTop < 0 is impossible.
    have : ¬ BitVec.ult uTop (0 : Word) := by
      rw [BitVec.ult_eq_decide]
      simp
    exact this hborrow
  exact mulsubN4_c3_ne_zero_imp_one hbnz hq_over h_c3_nz

/-- `MulsubBltC3OneOfCarryZero` under the addback-path selection. -/
theorem MulsubBltC3OneOfCarryZero_of_borrow_and_plus_one
    (uHi uLo vTop : Word)
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop_w : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat uHi uLo vTop).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 1)
    (hborrow : BitVec.ult uTop_w
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2) :
    MulsubBltC3OneOfCarryZero uHi uLo vTop v0 v1 v2 v3 u0 u1 u2 u3 := by
  show _ → _
  intro _
  have h_c3_nz :
      (mulsubN4 (divKTrialCallV4QHat uHi uLo vTop) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 ≠ 0 := by
    intro h0
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop_w (0 : Word) := by
      rw [BitVec.ult_eq_decide]
      simp
    exact this hborrow
  exact mulsubN4_c3_ne_zero_imp_one hbnz hq_over h_c3_nz

end EvmAsm.Evm64
