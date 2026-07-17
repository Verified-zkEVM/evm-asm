/-
  EvmAsm.Rv64.SAsm.ContForwardJoin

  The **plain forward-join to a shared continuation**
  (bead evm-asm-4ch8f.33.2.1 / evm-asm-4ch8f.33.2).

  `RetForwardJoin` (#10041) routes guard stations into shared RETURN
  tails.  Routines like `check_gas_limit` also contain the plain if/else
  shape whose two arms reconverge at a shared CONTINUATION — code that
  keeps executing after the join:

  ```
        bltu a1, a0, .else
        sub  t2, a1, a0        -- then:  t2 = parent - new
        j    .join
  .else: sub t2, a0, a1        -- else:  t2 = new - parent
  .join: bgeu t2, t1, …        -- both paths continue here
  ```

  At the structured layer neither `Stmt.retIf` (return tails only) nor
  `while2BreakJoin` (loop-specific) expresses this.  At `cpsTripleWithin`
  level the shape needs no new machinery — `retJoinStation_spec`'s "ret"
  is just an exit ADDRESS, so instantiating it at the join gives exactly
  the if/else combinator.  This module names that instantiation
  (`contJoinStation_spec`) so consumers and future porting agents find
  it, and adds the 0-step `cpsTripleWithin_stay` for arms whose branch
  target IS the join (the "skip" arm of an if with no else code).

  The two arms receive the decided branch fact as a plain hypothesis and
  prove the SAME join post `Q` — typically pinning the join register to
  an `if`-value (e.g. `t2 = |new − parent|` above), which downstream
  code consumes without caring which arm ran.

  Consumer: `check_gas_limit`
  (`Codegen/Programs/CheckGasLimitSAsm.lean`) — the abs-delta join
  feeding a `BGEU` guard and three shared return tails.

  Everything additive, at `cpsTripleWithin` level.
-/

import EvmAsm.Rv64.SAsm.RetForwardJoin

namespace EvmAsm.Rv64.SAsm

open EvmAsm.Rv64

/-- **One continuation-join station** — the non-terminating analog of
    `retJoinStation_spec`: a conditional branch whose two arms reconverge
    at a shared JOIN address (ordinary continuation code, not a return
    tail) with a common post `Q`.  Each arm consumes the decided branch
    fact as a hypothesis; `Q` typically pins the join register to an
    `if`-value both arms establish on their own side.  Definitionally the
    same composition as `retJoinStation_spec` — the exit is an address
    parameter, nothing about it is return-specific. -/
theorem contJoinStation_spec {n m : Nat} {addr tgtT tgtF join : Word}
    {cr : CodeReq} {P Qt Qf PT PF Q : Assertion} {cond : Prop}
    (hbr : cpsBranchWithin n addr cr P tgtT Qt tgtF Qf)
    (hentT : ∀ h, Qt h → (⌜cond⌝ ** PT) h)
    (hentF : ∀ h, Qf h → (⌜¬ cond⌝ ** PF) h)
    (htaken : cond → cpsTripleWithin m tgtT join cr PT Q)
    (hfall : ¬ cond → cpsTripleWithin m tgtF join cr PF Q) :
    cpsTripleWithin (n + m) addr join cr P Q :=
  retJoinStation_spec hbr hentT hentF htaken hfall

/-- The 0-step triple at a join point: a branch arm whose target IS the
    join continues immediately (the "skip" arm of an if without else
    code).  Any step bound. -/
theorem cpsTripleWithin_stay (n : Nat) (addr : Word) (cr : CodeReq)
    (P : Assertion) :
    cpsTripleWithin n addr addr cr P P :=
  fun _R _hR s _hcr h hpc => ⟨0, Nat.zero_le _, s, rfl, hpc, h⟩


end EvmAsm.Rv64.SAsm
