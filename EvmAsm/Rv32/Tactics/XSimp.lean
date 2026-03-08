/-
  EvmAsm.Rv32.Tactics.XSimp

  Higher-level separation logic tactics built on xperm, inspired by the
  `xsimpl` tactic from SPlean / CFML (see XPerm.lean for full references).

  - `xperm_hyp h`: Given hypothesis `h : P s`, proves goal `Q s` where Q is
    an AC-permutation of P. Drop-in replacement for `sep_perm h`.

  - `xsimp`: Proves goals of the form `∀ h, P h → Q h` (i.e., `himpl P Q`)
    where Q is an AC-permutation of P.
-/

import Lean
import EvmAsm.Rv32.Tactics.XPerm

open Lean Meta Elab Tactic

namespace EvmAsm.Tactics

/-- `xperm_hyp h` closes a goal of the form `Q s` given hypothesis `h : P s`
    where P and Q are AC-permutations of sepConj chains.

    Uses the same strategy as `sep_perm`: constructs
      `exact (congrFun (show _ = _ by xperm) _).mp h`
    which lets Lean's unifier determine P and Q from context, then uses
    `xperm` to prove the equality `P = Q`. -/
macro "xperm_hyp" hyp:ident : tactic =>
  `(tactic| exact (congrFun (show _ = _ by xperm) _).mp $hyp)

/-- `xsimp` proves goals of the form `∀ h, P h → Q h` or `himpl P Q`
    where Q is an AC-permutation of P. -/
elab "xsimp" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  -- Try to match `himpl P Q`
  if Expr.isAppOfArity goalType ``EvmAsm.himpl 2 then
    let p := Expr.appArg! (Expr.appFn! goalType)
    let q := Expr.appArg! goalType
    let eqProof ← buildPermProof p q
    let result := mkApp (mkApp (mkConst ``EvmAsm.himpl_of_eq) p) q
    goal.assign (mkApp result eqProof)
  else
    -- Assume it's `∀ h, P h → Q h`: introduce and use xperm_hyp
    evalTactic (← `(tactic| intro _ _hp; xperm_hyp _hp))

end EvmAsm.Tactics
