/-
  EvmAsm.Evm64.EvmWordArith.DivBltBridgeSpecializations

  Predicate-level BLT bridges for the N2 and N3 lanes.

  The bead-level BLT predicates are `loopBodyN{2,3}CallAddbackCarry2NzV4`,
  which expand to `isAddbackCarry2Nz (divKTrialCallV4QHat …) …` with the
  lane-specific `(uHi, uLo, vTop)` triple.  Here we unfold those defs once
  and apply the generic BLT bridge `isAddbackCarry2Nz_blt_of_overestimate_…`
  from `DivBltBridge`.

  The result: closure-form theorems
    • `loopBodyN2CallAddbackCarry2NzV4_of_…`
    • `loopBodyN3CallAddbackCarry2NzV4_of_…`
  with the same three named inputs as the BLT bridge.  Mirrors the
  MAX-side `isAddbackCarry2NzN{2,3}Max_of_not_ult_c3_one_of_carry_zero`.
-/

module

public import EvmAsm.Evm64.EvmWordArith.DivBltBridge
public import EvmAsm.Evm64.DivMod.LoopIterN2AddbackV4NoNop
public import EvmAsm.Evm64.DivMod.LoopIterN3AddbackV4NoNop

public section

namespace EvmAsm.Evm64

open EvmWord EvmAsm.Rv64

/-- N2 BLT bridge: `loopBodyN2CallAddbackCarry2NzV4` predicate form from the
    +2 v4 overestimate, the divisor-nonzero fact, and the named BLT c3
    invariant.  The v4 trial is `divKTrialCallV4QHat u2 u1 v1`. -/
theorem loopBodyN2CallAddbackCarry2NzV4_of_overestimate_c3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat u2 u1 v1).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3 : MulsubBltC3OneOfCarryZero u2 u1 v1 v0 v1 v2 v3 u0 u1 u2 u3) :
    loopBodyN2CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopBodyN2CallAddbackCarry2NzV4
  exact isAddbackCarry2Nz_blt_of_overestimate_c3_one_of_carry_zero
    u2 u1 v1 v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over hc3

/-- N3 BLT bridge: `loopBodyN3CallAddbackCarry2NzV4` predicate form from the
    +2 v4 overestimate, the divisor-nonzero fact, and the named BLT c3
    invariant.  The v4 trial is `divKTrialCallV4QHat u3 u2 v2`. -/
theorem loopBodyN3CallAddbackCarry2NzV4_of_overestimate_c3
    (v0 v1 v2 v3 u0 u1 u2 u3 uTop : Word)
    (hbnz : v0 ||| v1 ||| v2 ||| v3 ≠ 0)
    (hq_over : (divKTrialCallV4QHat u3 u2 v2).toNat ≤
      val256 u0 u1 u2 u3 / val256 v0 v1 v2 v3 + 2)
    (hc3 : MulsubBltC3OneOfCarryZero u3 u2 v2 v0 v1 v2 v3 u0 u1 u2 u3) :
    loopBodyN3CallAddbackCarry2NzV4 v0 v1 v2 v3 u0 u1 u2 u3 uTop := by
  unfold loopBodyN3CallAddbackCarry2NzV4
  exact isAddbackCarry2Nz_blt_of_overestimate_c3_one_of_carry_zero
    u3 u2 v2 v0 v1 v2 v3 u0 u1 u2 u3 uTop hbnz hq_over hc3

end EvmAsm.Evm64
