/-
  EvmAsm.Evm64.DivMod.Spec.N2V5CallCarryFromBorrow

  `callAddbackCarry2NzV5` from `c3 = 1` (the borrow-case fact) plus the `+2`
  overestimate.  This is the correct discharge of the call-digit carry: it is
  needed only on the ADDBACK branch of the loop's per-digit borrow dispatch,
  where `c3 = 1` holds (borrow ⟹ c3 ≠ 0, and the n2 normalized divisor
  `val256 v < 2^128` forces `c3 ≤ 1`, so `c3 = 1`).  In the no-borrow branch the
  loop takes the SKIP body (`mulsubN4NoBorrow`) and no carry2nz is required.

  This replaces the over-strong `loopN2SelectedCarryV5` hypothesis (which asserts
  carry2nz unconditionally — false when a call digit's trial is exact, `c3 = 0`).
-/

module

public import EvmAsm.Evm64.DivMod.Spec.N2V5CallAddbackOverestimate

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- `callAddbackCarry2NzV5` from the `+2` overestimate and `c3 = 1`.  Since
    `c3 = 1`, the `carry = 0 → c3 = 1` invariant is immediate, so the call carry
    follows from `callAddbackCarry2NzV5_of_overestimate_c3` (#7424). -/
theorem callAddbackCarry2NzV5_of_c3_eq_one
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV5QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3 : (mulsubN4 (divKTrialCallV5QHat u2 u1 v1) v0 v1 v2 v3 u0 u1 u2 u3).2.2.2.2 = 1) :
    callAddbackCarry2NzV5 v0 v1 v2 v3 u0 u1 u2 u3 uTop :=
  callAddbackCarry2NzV5_of_overestimate_c3 v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over
    (fun _ => hc3)

end EvmAsm.Evm64
