/-
  EvmAsm.Progress.CycleBounds

  Kernel-checked binding of the opcode registry's `cycleBound` field to the
  step bound that the witness theorem *actually* proves (GH #10552; the
  follow-up deferred in the `cycleBound` docstring of `EvmAsm/Progress.lean`).

  ## The hole this closes

  `OpcodeEntry.cycleBound` records each opcode's worst-case `cpsTripleWithin N`
  step bound as a hand-copied literal. Before this module, nothing tied that
  literal to the theorem: the registry could say `some 30` while
  `evm_add_stack_spec_within` proved `cpsTripleWithin 100`, and the only signal
  would be a registry-vs-registry diff in the rendered report — i.e. a
  divergence between the registry and the *proof* was invisible. The registry is
  the source the C.1 cycle-budget surrogate is read from, so a silent inflation
  there is a silently wrong resource claim.

  ## What is checked, and by whom

  For each registry row whose `cycleBound` is `some N`, `pin_cycle_bound` emits
  **two** declarations:

  1. `<OP>_cycleBound_registry : cycleBoundOf "<OP>" = some N := by decide`
     — where `N` is *not* written by hand: the command reads the witness
     theorem's elaborated type out of the environment, finds the `cps*Within`
     application in its conclusion, evaluates the step-bound argument, and
     writes that value into the statement. The `decide` is kernel-checked, so
     the registry row and the theorem's own bound are equal by kernel
     computation over `EvmAsm.Progress.registry`.
  2. `<OP>_cycleBound_pinned : <the theorem's own type, with the step-bound
     argument replaced by `cycleBoundNat "<OP>"`> := <the theorem>`
     — the theorem constant itself is offered at a type that names the
     *registry* rather than a literal. The kernel must reduce
     `cycleBoundNat "<OP>"` through `registry` and find it definitionally equal
     to the bound the theorem proves. This is the direction that makes the
     binding kernel-checked rather than elaborator-checked: nothing in the
     emitted term mentions `N`.

  Declaration (2) is what bites on a bound *inflation*; declaration (1) is what
  bites on a row being renamed, retargeted, or dropped (it rules out the
  `cycleBoundOf … = none` case that `cycleBoundNat`'s `getD` would otherwise
  paper over).

  Note that the two bounds that are stated in closed form rather than as
  literals (`MULMOD`'s `8 + (440 + …)`, `EXP`'s `29 + 256 * 193 + 10`) are
  pinned the same way and get a slightly stronger statement for free: the
  registry literal is tied to the *evaluated* closed form.

  ## Coverage

  A pin only helps rows that have one. `#cycle_bounds_cover_registry` at the
  bottom of this file walks `registry` itself and fails the build if any row
  with a literal `cycleBound` lacks both emitted declarations — so a new row
  that records a bound cannot land unpinned. Rows with `cycleBound = none`
  (`DIV`/`MOD`'s `unifiedDivBound`, the `execSpec` rows with no triple at all)
  are outside the claim by construction and are not gated; `cycleBoundRows_eq`
  records how many rows are in scope, so the scope itself moves visibly.

  A pin must also name the theorem its own row's `proofRef` names: otherwise
  pinning `evm_shr_stack_spec_within` under the `SHL` row would pass (both prove
  46) while binding the row's bound to the wrong proof.

  ## Why this is Lean and not a `grep` gate

  A source-scanning gate would have to re-parse `cpsTripleWithin <N>` out of
  `.lean` text, which loses on exactly the cases that matter: bounds stated as
  arithmetic, bounds reached through a wrapper, and theorems whose conclusion
  is not textually adjacent to their name. Reading the elaborated type from the
  environment has none of those failure modes, and a mismatch is a build
  failure rather than a script that has to be remembered and wired.
-/

import EvmAsm.Progress
import Lean

namespace EvmAsm.Progress

/-! ## Registry accessors

    Both are plain `def`s (not `abbrev`s): the kernel unfolds them by delta
    when checking the pins, and keeping them opaque to `simp` avoids
    perturbing unrelated proofs. -/

/-- The step bound recorded in the registry for the row named `name`, or `none`
    if there is no such row or the row records no literal bound. -/
def cycleBoundOf (name : String) : Option Nat :=
  (registry.find? (fun e => e.name == name)).bind (·.cycleBound)

/-- Total form of `cycleBoundOf`, for use in a `cps*Within` position. The `0`
    default is never load-bearing: every emitted pin is accompanied by a
    `cycleBoundOf … = some N` theorem, which rules out the `none` branch. -/
def cycleBoundNat (name : String) : Nat := (cycleBoundOf name).getD 0

/-- The witness theorem *named* by the row `name`. Used by `pin_cycle_bound` to
    reject a pin that binds a row's bound to some other opcode's theorem. -/
def proofRefOf (name : String) : Option String :=
  (registry.find? (fun e => e.name == name)).bind (·.proofRef)

namespace CycleBounds

open Lean Meta Elab Command

/-- The bounded CPS spec heads. In all four, `nSteps` is the first explicit
    argument, so the step bound is argument 0 of the application. -/
private def cpsHeads : List Name :=
  [``EvmAsm.Rv64.cpsTripleWithin, ``EvmAsm.Rv64.cpsBranchWithin,
   ``EvmAsm.Rv64.cpsNBranchWithin, ``EvmAsm.Rv64.cpsHaltTripleWithin]

/-- Strip `∀`/`let`/`mdata` down to the conclusion. Hypotheses are deliberately
    *not* searched: a staged spec that takes a triple as a hypothesis would
    otherwise contribute a second, unrelated step bound. -/
private partial def conclusionOf : Expr → Expr
  | .forallE _ _ b _ => conclusionOf b
  | .letE _ _ _ b _ => conclusionOf b
  | .mdata _ e => conclusionOf e
  | e => e

/-- `some (head, args)` when `e` is an application of one of `cpsHeads`. -/
private def cpsApp? (e : Expr) : Option (Name × Array Expr) :=
  match e.getAppFn with
  | .const n _ => if cpsHeads.contains n then some (n, e.getAppArgs) else none
  | _ => none

/-- Rebuild a type, applying `f` to its conclusion and keeping the binder
    structure (and hence the sharing) intact. -/
private partial def mapConclusion (f : Expr → MetaM Expr) : Expr → MetaM Expr
  | .forallE n t b bi => return .forallE n t (← mapConclusion f b) bi
  | .letE n t v b nd => return .letE n t v (← mapConclusion f b) nd
  | .mdata d e => return .mdata d (← mapConclusion f e)
  | e => f e

/-- Sanitised identifier stem for a registry row name (`PUSH2..32` →
    `PUSH2__32`). -/
def stem (name : String) : String :=
  name.map fun c => if c.isAlphanum then c else '_'

/-- Name of the emitted `cycleBoundOf … = some N` theorem for row `name`. -/
def registryPinName (name : String) : Name :=
  `EvmAsm.Progress.CycleBounds ++ Name.mkSimple (stem name ++ "_cycleBound_registry")

/-- Name of the emitted registry-typed restatement of the witness theorem. -/
def theoremPinName (name : String) : Name :=
  `EvmAsm.Progress.CycleBounds ++ Name.mkSimple (stem name ++ "_cycleBound_pinned")

/-- Reduce `e` to a `Nat` literal, or fail. Handles both the raw-literal form
    and the `OfNat.ofNat`-wrapped form a source literal elaborates to. -/
private def evalNatLit (what : String) (e : Expr) : MetaM Nat := do
  let e' ← whnf e
  match e'.rawNatLit?.orElse fun _ => e'.nat? with
  | some n => return n
  | none => throwError "pin_cycle_bound: {what} does not evaluate to a Nat literal:{indentExpr e}"

/--
`pin_cycle_bound "OP" thm` binds the registry's `cycleBound` for the row named
`OP` to the step bound proven by `thm`.

Reads `thm`'s elaborated type from the environment, locates the `cps*Within`
application in its conclusion, and emits

* `OP_cycleBound_registry : cycleBoundOf "OP" = some <bound> := by decide`, and
* `OP_cycleBound_pinned : <thm's type, with the bound replaced by
  `cycleBoundNat "OP"`> := thm`.

Errors (loudly, at elaboration) if `thm` is unknown, if its conclusion has no
`cps*Within` head, if the step bound is not a closed `Nat`, if the registry has
no row named `OP`, if that row records no `cycleBound`, or if the two values
disagree. There is no "found nothing, so pass" path.
-/
syntax (name := pinCycleBound) "pin_cycle_bound " str ppSpace ident : command

@[command_elab pinCycleBound]
def elabPinCycleBound : CommandElab := fun stx => do
  match stx with
  | `(pin_cycle_bound $nameStx:str $thmStx:ident) => do
    let opName := nameStx.getString
    let thmName ← liftCoreM <| realizeGlobalConstNoOverload thmStx
    let (thmBound, pinnedType) ← liftTermElabM do
      let some info := (← getEnv).find? thmName
        | throwError "pin_cycle_bound: unknown declaration {thmName}"
      -- 1. The bound the theorem actually proves.
      let concl := conclusionOf info.type
      let some (_, args) := cpsApp? concl
        | throwError
            "pin_cycle_bound: the conclusion of {thmName} is not an application of \
             one of {cpsHeads}; it is:{indentExpr concl}"
      let some boundExpr := args[0]?
        | throwError "pin_cycle_bound: {thmName}'s CPS application has no step-bound argument"
      let thmBound ← evalNatLit s!"the step bound of {thmName}" boundExpr
      -- 2. The bound the registry records. Checked here for a readable error;
      --    the emitted `by decide` is what makes it kernel truth.
      let regBound ←
        evalNatLit s!"cycleBoundNat \"{opName}\""
          (mkApp (mkConst ``EvmAsm.Progress.cycleBoundNat) (mkStrLit opName))
      let regOpt ← whnf (mkApp (mkConst ``EvmAsm.Progress.cycleBoundOf) (mkStrLit opName))
      unless regOpt.isAppOf ``Option.some do
        throwError
          "pin_cycle_bound: registry has no row named \"{opName}\" carrying a literal \
           `cycleBound` (`cycleBoundOf` reduced to{indentExpr regOpt}). \
           {thmName} proves `cpsTripleWithin {thmBound}`."
      unless regBound == thmBound do
        throwError
          "pin_cycle_bound: registry/theorem cycle-bound mismatch for \"{opName}\": \
           registry says {regBound}, but {thmName} proves a bound of {thmBound}. \
           Fix the `(cycleBound := some …)` field in EvmAsm/Progress.lean, or the theorem."
      -- 2b. The pin must bind the row's *own* witness theorem. Without this,
      --     pinning SHR's theorem for the SHL row would pass (both prove 46) —
      --     i.e. the bound would be bound to the wrong proof. `proofRef` is
      --     stored partially qualified, so a component-suffix match is the
      --     right comparison.
      let refExpr ← whnf (mkApp (mkConst ``EvmAsm.Progress.proofRefOf) (mkStrLit opName))
      match refExpr.getAppArgs[1]? with
      | some (Expr.lit (Literal.strVal ref)) =>
        let full := thmName.toString
        unless full == ref || full.endsWith ("." ++ ref) do
          throwError
            "pin_cycle_bound: row \"{opName}\" names `{ref}` as its witness, but this pin \
             binds its cycle bound to {thmName}. Pin the row's own theorem (or update the \
             row's `proofRef`)."
      | _ =>
        throwError
          "pin_cycle_bound: row \"{opName}\" records a `cycleBound` but no `proofRef`, so \
           there is no theorem to bind it to.{indentExpr refExpr}"
      -- 3. The registry-typed restatement: same type, with the literal bound
      --    replaced by the registry lookup. Nothing here mentions the literal,
      --    so the kernel has to reduce the registry to accept the declaration.
      let regTerm := mkApp (mkConst ``EvmAsm.Progress.cycleBoundNat) (mkStrLit opName)
      let pinnedType ← mapConclusion (fun e => do
          let some (_, args) := cpsApp? e
            | throwError "pin_cycle_bound: internal: conclusion changed shape"
          return mkAppN e.getAppFn (args.set! 0 regTerm)) info.type
      return (thmBound, pinnedType)
    -- Emit (1) via ordinary elaboration so the `decide` proof term is built the
    -- usual way, and (2) by `addDecl` (its type is an `Expr`, not syntax).
    -- `_root_` because the pin sites sit inside `namespace EvmAsm.Progress`.
    let regPin := mkIdent (`_root_ ++ registryPinName opName)
    elabCommand (← `(command|
      theorem $regPin : EvmAsm.Progress.cycleBoundOf $(quote opName) = some $(quote thmBound) := by
        decide))
    liftTermElabM do
      let some info := (← getEnv).find? thmName
        | throwError "pin_cycle_bound: unknown declaration {thmName}"
      addDecl <| .thmDecl
        { name := theoremPinName opName
          levelParams := info.levelParams
          type := pinnedType
          value := mkConst thmName (info.levelParams.map .param) }
  | _ => throwUnsupportedSyntax

/-- Walk `e` as a `List` literal, returning its elements. -/
private partial def listElems (e : Expr) : MetaM (List Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, args) =>
    match args[1]?, args[2]? with
    | some h, some t => return h :: (← listElems t)
    | _, _ => throwError "cycle-bound coverage: malformed List.cons:{indentExpr e}"
  | _ => throwError "cycle-bound coverage: not a list literal:{indentExpr e}"

/--
`#cycle_bounds_cover_registry` fails the build if any `registry` row with a
literal `cycleBound` is missing its `pin_cycle_bound` declarations. This is the
half that stops a *new* row from landing unpinned; the pins themselves only
speak about the rows they name.
-/
elab "#cycle_bounds_cover_registry" : command => do
  let missing ← liftTermElabM do
    let rows ← listElems (mkConst ``EvmAsm.Progress.registry)
    let env ← getEnv
    let mut missing : List String := []
    for row in rows do
      let nameExpr ← whnf (mkApp (mkConst ``EvmAsm.Progress.OpcodeEntry.name) row)
      let .lit (.strVal rowName) := nameExpr
        | throwError "cycle-bound coverage: row name is not a string literal:{indentExpr nameExpr}"
      let boundExpr ← whnf (mkApp (mkConst ``EvmAsm.Progress.OpcodeEntry.cycleBound) row)
      if boundExpr.isAppOf ``Option.some then
        unless env.contains (registryPinName rowName) && env.contains (theoremPinName rowName) do
          missing := missing ++ [rowName]
    return missing
  unless missing.isEmpty do
    throwError
      "cycle-bound coverage: {missing.length} registry row(s) record a literal `cycleBound` \
       but have no `pin_cycle_bound` line in EvmAsm/Progress/CycleBounds.lean: \
       {missing}. Add one (or drop the row's `cycleBound`)."

end CycleBounds

/-! ## The pins

    One line per registry row that records a literal `cycleBound`. The bound is
    deliberately absent from these lines: it is read out of the theorem. -/

section Pins

pin_cycle_bound "STOP" EvmAsm.Evm64.Terminating.evm_stop_stack_spec_within
pin_cycle_bound "ADD" EvmAsm.Evm64.evm_add_stack_spec_within
pin_cycle_bound "MUL" EvmAsm.Evm64.evm_mul_stack_spec_within
pin_cycle_bound "SUB" EvmAsm.Evm64.evm_sub_stack_spec_within
pin_cycle_bound "MULMOD" EvmAsm.Evm64.MulMod.Compose.evm_mulmod_stack_spec_within
pin_cycle_bound "EXP" EvmAsm.Evm64.evm_exp_stack_spec_within
pin_cycle_bound "SIGNEXTEND" EvmAsm.Evm64.evm_signextend_stack_spec_within
pin_cycle_bound "LT" EvmAsm.Evm64.evm_lt_stack_spec_within
pin_cycle_bound "GT" EvmAsm.Evm64.evm_gt_stack_spec_within
pin_cycle_bound "SLT" EvmAsm.Evm64.evm_slt_stack_spec_within
pin_cycle_bound "SGT" EvmAsm.Evm64.evm_sgt_stack_spec_within
pin_cycle_bound "EQ" EvmAsm.Evm64.evm_eq_stack_spec_within
pin_cycle_bound "ISZERO" EvmAsm.Evm64.evm_iszero_stack_spec_within
pin_cycle_bound "AND" EvmAsm.Evm64.evm_and_stack_spec_within
pin_cycle_bound "OR" EvmAsm.Evm64.evm_or_stack_spec_within
pin_cycle_bound "XOR" EvmAsm.Evm64.evm_xor_stack_spec_within
pin_cycle_bound "NOT" EvmAsm.Evm64.evm_not_stack_spec_within
pin_cycle_bound "BYTE" EvmAsm.Evm64.evm_byte_stack_spec_within
pin_cycle_bound "SHL" EvmAsm.Evm64.evm_shl_stack_spec_within
pin_cycle_bound "SHR" EvmAsm.Evm64.evm_shr_stack_spec_within
pin_cycle_bound "SAR" EvmAsm.Evm64.evm_sar_stack_spec_within
pin_cycle_bound "BLOCKHASH" EvmAsm.Evm64.BlockHash.evm_blockhash_stack_spec_within
pin_cycle_bound "BLOBHASH" EvmAsm.Evm64.BlobHash.evm_blobhash_stack_spec_within
pin_cycle_bound "POP" EvmAsm.Evm64.evm_pop_stack_spec_within
pin_cycle_bound "MSTORE8" EvmAsm.Evm64.evm_mstore8_stack_spec_within
pin_cycle_bound "JUMP" EvmAsm.Evm64.ControlFlow.evm_jump_stack_spec_within
pin_cycle_bound "JUMPI" EvmAsm.Evm64.ControlFlow.evm_jumpi_stack_spec_within
pin_cycle_bound "MSIZE" EvmAsm.Evm64.evm_msize_stack_spec_within
pin_cycle_bound "JUMPDEST" EvmAsm.Evm64.ControlFlow.evm_jumpdest_stack_spec_within
pin_cycle_bound "PUSH0" EvmAsm.Evm64.evm_push0_stack_spec_within
pin_cycle_bound "INVALID" EvmAsm.Evm64.Terminating.evm_invalid_stack_spec_within
pin_cycle_bound "SELFDESTRUCT" EvmAsm.Evm64.Terminating.evm_selfdestruct_stack_spec_resolved

#cycle_bounds_cover_registry

/-- How many registry rows record a literal `cycleBound` — i.e. how many rows
    the pins above speak about. `decide`-checked so that a row *gaining* a
    bound is a visible diff here as well as a coverage error. -/
theorem cycleBoundRows_eq :
    (registry.filter (fun e => e.cycleBound.isSome)).length = 32 := by decide

end Pins

end EvmAsm.Progress
