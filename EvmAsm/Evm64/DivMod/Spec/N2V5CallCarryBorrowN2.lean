/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryBorrowN2

  `callAddbackCarry2NzV5_of_borrow_n2`: the call-digit carry discharged purely
  from the runtime borrow + n2 shape facts, with NO unconditional carry2nz
  hypothesis.  On the addback (borrow) branch of the loop's per-digit dispatch,
  the borrow check `BitVec.ult uTop (mulsubN4_c3 …)` gives `c3 ≠ 0`; the n2
  small-divisor `c3 ≤ 1` bound (#7430) then forces `c3 = 1`, which discharges
  `callAddbackCarry2NzV5` via `callAddbackCarry2NzV5_of_c3_eq_one` (#7428).

  This is what lets the loop's call body drop the over-strong `hcarry2_nz`
  hypothesis (false in the no-borrow / exact case): carry2nz is needed only in
  the borrow branch, where it is now derived from shape.
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryFromBorrow
public import EvmAsm.Evm64.DivMod.Spec.N2V5C3LeOne

@[expose] public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `callAddbackCarry2NzV5` from the `+2` overestimate, the n2 small-divisor
    bound, and the runtime borrow check `BitVec.ult uTop (mulsubN4_c3 …) = true`. -/
theorem callAddbackCarry2NzV5_of_borrow_n2
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hv_small : 2 * val256 v0 v1 v2 v3 < 2 ^ 256)
    (hborrow : BitVec.ult uTop
      (mulsubN4_c3 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3) = true) :
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  apply callAddbackCarry2NzV5_of_c3_eq_one v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over
  have hle1 := mulsubN4_c3_le_one_of_plus_two_of_v_lt hbnz hq_over hv_small
  have hne0 : (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 ≠ 0 := by
    intro h0
    unfold mulsubN4_c3 at hborrow
    rw [h0] at hborrow
    have : ¬ BitVec.ult uTop (0 : Word) := by rw [BitVec.ult_eq_decide]; simp
    exact this hborrow
  have hne0' :
      (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat ≠ 0 := by
    intro hz
    exact hne0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
  apply BitVec.eq_of_toNat_eq
  show (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2.toNat = 1
  omega

end EvmAsm.Evm64
