/-
  EvmAsm.Rv64.Tactics.XPermCert

  Standalone opt-in surface for the YOLO-style certificate permutation prover.

  The prover itself (`buildPermProofCert`) and the `xperm.cert` option live in
  `XPerm.lean`, so that the whole `xperm` family can dispatch on the option
  without an import cycle. This file only exposes test/diagnostic tactics that
  invoke the certificate prover *directly* (bypassing the option), so it can be
  exercised regardless of the `xperm.cert` setting.
-/

import EvmAsm.Rv64.Tactics.XPerm

open Lean Meta Elab Tactic

namespace EvmAsm.Rv64.Tactics

/-- `xperm_cert_eq` proves `⊢ P = Q` where `P` and `Q` are AC-permutations of
    `sepConj` chains, via the certificate prover (regardless of `xperm.cert`). -/
elab "xperm_cert_eq" : tactic => do
  let goal ← getMainGoal
  let some (_, l, r) := (← goal.getType).eq?
    | throwError "xperm_cert_eq: goal is not an equality"
  goal.assign (← buildPermProofCert l r)

/-- `xperm_cert h`: like `xperm_hyp h`, but always routes through the
    certificate prover. Given `h : P s`, closes `Q s` when `P` and `Q` are
    `sepConj` permutations. -/
macro "xperm_cert" hyp:ident : tactic =>
  `(tactic| exact (congrFun (show _ = _ by xperm_cert_eq) _).mp $hyp)

end EvmAsm.Rv64.Tactics
