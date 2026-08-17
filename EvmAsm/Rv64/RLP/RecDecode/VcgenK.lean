/-
  A `vcgen` variant that never attempts `decide` during splitting: all VCs
  (including decidable bookkeeping ones) become named goals, to be closed
  by the caller with `decide +kernel`.  Exists because the stock tactic's
  elaborator-side `whnf (decide _)` on large flatten/offset computations
  cannot fit a 200k-heartbeat budget.
-/
import Lean
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64
namespace SAsm

open Lean Elab Tactic Meta

private partial def evalLabelK (e : Expr) : MetaM String := do
  let e ← do
    match ← whnfUntil e ``String.append with
    | some e' => Pure.pure e'
    | none => whnf e
  match e with
  | .lit (.strVal s) => return s
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``HAppend.hAppend && args.size == 6 then
      return (← evalLabelK args[4]!) ++ (← evalLabelK args[5]!)
    else if f.isConstOf ``String.append && args.size == 2 then
      return (← evalLabelK args[0]!) ++ (← evalLabelK args[1]!)
    else
      throwError "vcgenK: cannot evaluate VC label{indentExpr e}"

private def labelToNameK (label : String) : Name :=
  (label.splitOn ".").foldl (fun n s => Name.str n s) Name.anonymous

private partial def vcCasesK (g : MVarId) : MetaM (List MVarId) := do
  g.withContext do
    let t ← g.getType
    unless t.isAppOfArity ``VCs.Hold 1 do
      throwError "vcgenK: expected a `VCs.Hold` goal, got{indentExpr t}"
    let e ← whnf t.appArg!
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``List.nil then
      g.assign (← mkAppOptM ``VCs.Hold.nil #[])
      return []
    else if f.isConstOf ``List.cons && args.size == 3 then
      let vc := args[1]!
      let g ← g.change (mkApp (mkConst ``VCs.Hold) e)
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``VCs.Hold.cons_intro)
      match gs with
      | [gHead, gTail] =>
          let vc' ← whnf vc
          let gHead ←
            if vc'.isAppOfArity ``VC.mk 2 then do
              let label ← evalLabelK (vc'.getAppArgs[0]!)
              let gHead ← gHead.change (← whnf (← gHead.getType))
              gHead.setTag (labelToNameK label)
              Pure.pure gHead
            else
              Pure.pure gHead
          return gHead :: (← vcCasesK gTail)
      | _ => throwError "vcgenK: unexpected goals from Hold.cons_intro"
    else if (f.isConstOf ``HAppend.hAppend && args.size == 6)
        || (f.isConstOf ``List.append && args.size == 2) then
      let g ← g.change (mkApp (mkConst ``VCs.Hold) e)
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``VCs.Hold.append_intro)
      match gs with
      | [g1, g2] => return (← vcCasesK g1) ++ (← vcCasesK g2)
      | _ => throwError "vcgenK: unexpected goals from Hold.append_intro"
    else
      throwError "vcgenK: VC list does not reduce to a cons/append spine; \
        stuck on{indentExpr e}"

elab "vcgenK" : tactic => do
  let tgt ← getMainTarget
  if tgt.isAppOf ``Fn.SpecR then
    evalTactic (← `(tactic|
      refine EvmAsm.Rv64.SAsm.Fn.soundR _ _ _ ?region ?code ?callees ?calls ?_))
  else
    evalTactic (← `(tactic| refine EvmAsm.Rv64.SAsm.Fn.sound _ _ ?region ?_))
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    if (← g.getType).isAppOfArity ``VCs.Hold 1 then
      out := out ++ (← vcCasesK g)
    else
      out := out ++ [g]
  replaceMainGoal out

end SAsm
end EvmAsm.Rv64
