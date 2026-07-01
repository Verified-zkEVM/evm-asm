/-
  EvmAsm.Rv64.SAsm.Tactic

  The `vcgen` tactic: applies `Fn.sound` and splits the function's VC list
  into one *named* goal per verification condition.  Each goal is pure; its
  case name is the VC's path label (e.g. `memcpy.copy.inv_step`).

  Recursion safety by construction (docs/sasm-design.md §3.8): the VC list
  is computed by the structurally recursive `Fn.vcs`/`Stmt.vcs`, so the
  tactic only walks a cons/append spine whose length is linear in the AST —
  it never recurses over instructions, step counts, or loop fuel.  Decidable
  bookkeeping VCs (`.flat`, block `.ok`) are discharged automatically with
  `decide`.

  On failure the leftover named goals are the report: an unsupported
  instruction surfaces as a `blockOk … = true` goal naming the block, a
  wrong invariant as its `inv_step` goal, and (until M4) any `call` as an
  unprovable `…​.call_unsupported_until_M4 : False` goal.
-/

import Lean
import EvmAsm.Rv64.SAsm.Fn

namespace EvmAsm.Rv64
namespace SAsm

open Lean Elab Tactic Meta

/-- Evaluate a VC label expression: labels are built exclusively from string
    literals and `++`, so a tiny structural evaluator suffices. -/
private partial def evalLabel (e : Expr) : MetaM String := do
  -- Reduce, but stop at `String.append` (full whnf would unfold it into its
  -- ByteArray implementation).
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
      return (← evalLabel args[4]!) ++ (← evalLabel args[5]!)
    else if f.isConstOf ``String.append && args.size == 2 then
      return (← evalLabel args[0]!) ++ (← evalLabel args[1]!)
    else
      throwError "vcgen: cannot evaluate VC label{indentExpr e}"

/-- Turn a dotted label into a hierarchical case name. -/
private def labelToName (label : String) : Name :=
  (label.splitOn ".").foldl (fun n s => Name.str n s) Name.anonymous

/-- Split a `VCs.Hold …` goal along the cons/append spine of the VC list,
    naming each leaf goal by its label. -/
private partial def vcCases (g : MVarId) : MetaM (List MVarId) := do
  g.withContext do
    let t ← g.getType
    unless t.isAppOfArity ``VCs.Hold 1 do
      throwError "vcgen: expected a `VCs.Hold` goal, got{indentExpr t}"
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
          -- Name the head goal by its label and expose the raw proposition.
          let vc' ← whnf vc
          let gHead ←
            if vc'.isAppOfArity ``VC.mk 2 then do
              let label ← evalLabel (vc'.getAppArgs[0]!)
              let gHead ← gHead.change (← whnf (← gHead.getType))
              gHead.setTag (labelToName label)
              Pure.pure gHead
            else
              Pure.pure gHead
          return gHead :: (← vcCases gTail)
      | _ => throwError "vcgen: unexpected goals from Hold.cons_intro"
    else if (f.isConstOf ``HAppend.hAppend && args.size == 6)
        || (f.isConstOf ``List.append && args.size == 2) then
      let g ← g.change (mkApp (mkConst ``VCs.Hold) e)
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``VCs.Hold.append_intro)
      match gs with
      | [g1, g2] => return (← vcCases g1) ++ (← vcCases g2)
      | _ => throwError "vcgen: unexpected goals from Hold.append_intro"
    else
      throwError "vcgen: VC list does not reduce to a cons/append spine; \
        stuck on{indentExpr e}\n\
        Hint: is the function body a literal `Stmt` (plain `def`, not \
        irreducible)?"

/-- Apply `Fn.sound` and split the VC list into one named goal per
    verification condition.  Decidable bookkeeping VCs are closed with
    `decide`; the remaining goals carry their path labels as case names. -/
elab "vcgen" : tactic => do
  let tgt ← getMainTarget
  if tgt.isAppOf ``Fn.SpecR then
    -- Caller-shaped goal: code/callee containment and call-site address
    -- side conditions become their own named goals.
    evalTactic (← `(tactic|
      refine EvmAsm.Rv64.SAsm.Fn.soundR _ _ _ ?region ?code ?callees ?calls ?_))
  else
    evalTactic (← `(tactic| refine EvmAsm.Rv64.SAsm.Fn.sound _ _ ?region ?_))
  let gs ← getGoals
  let mut out : List MVarId := []
  let tryDecide (g : MVarId) : TacticM Bool := g.withContext do
    try
      let t ← g.getType
      -- Only accept when the decision procedure genuinely evaluates to
      -- `true` (mkDecideProof alone can produce kernel-rejected proofs on
      -- goals with free variables that do not reduce away).
      let d ← mkDecide t
      let r ← withDefault <| whnf d
      unless r.isConstOf ``Bool.true do
        return false
      let prf ← mkDecideProof t
      g.assign prf
      Pure.pure true
    catch _ =>
      Pure.pure false
  for g in gs do
    if (← g.getType).isAppOfArity ``VCs.Hold 1 then
      -- Split the VC list; auto-discharge decidable bookkeeping goals
      -- (kernel `decide`; free variables are fine because the checked
      -- terms reduce them away).
      for g' in ← vcCases g do
        unless ← tryDecide g' do
          out := out ++ [g']
    else if (← g.getTag).getRoot == `region then
      -- Region well-formedness is decidable for concrete regions.  Do NOT
      -- attempt `decide` on the other side goals: they quantify over full
      -- `Word`s, which is "decidable" by 2^64-case analysis and would melt
      -- the kernel.
      unless ← tryDecide g do
        out := out ++ [g]
    else
      out := out ++ [g]
  replaceMainGoal out

end SAsm
end EvmAsm.Rv64
