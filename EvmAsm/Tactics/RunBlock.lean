/-
  EvmAsm.Tactics.RunBlock

  Multi-instruction block verification tactic. Composes N single-instruction
  specs into a single cpsTriple proof with automatic framing, address
  normalization, and postcondition permutation.

  ## Quick Reference

  **Auto mode** (preferred — resolves specs from `@[spec_gen]` database):
  ```
  theorem my_block_spec ... :
      cpsTriple base (base + 12)
        ((base ↦ᵢ .LW .x7 .x12 off) ** ((base + 4) ↦ᵢ .ADD .x7 .x7 .x6) **
         ((base + 8) ↦ᵢ .SW .x12 .x7 off) ** (.x12 ↦ᵣ sp) ** ...)
        (... updated state ...) := by
    runBlock
  ```

  **Manual mode** (pass spec hypotheses explicitly):
  ```
  theorem my_composite_spec ... := by
    have s1 := sub_spec_phase1 ...
    have s2 := sub_spec_phase2 ...
    runBlock s1 s2
  ```

  ## How It Works

  1. Extracts `instrAt` atoms from the goal's precondition (in order)
  2. For each instruction, looks up matching `@[spec_gen]` specs and
     instantiates via unification against the current assertion state
  3. Frames the first spec against the goal's full precondition
  4. Chains specs via `seqFrame` with automatic address normalization
  5. Permutes the final postcondition to match the goal

  ## Debugging

  Enable tracing for detailed resolution output:
  ```
  set_option trace.runBlock true in
  theorem my_spec ... := by runBlock
  ```

  Use `#spec_db` (from SpecDb.lean) to inspect registered specs:
  ```
  #spec_db  -- prints all @[spec_gen] entries grouped by instruction
  ```

  ## When Auto Mode Fails

  Common reasons and fixes:
  - **Missing spec**: Check `#spec_db` for coverage. Add `@[spec_gen]` to your spec.
  - **Proof obligation unsolved**: Auto-mode handles `rd ≠ .x0`, `rd ≠ rs`, and
    `isValidMemAccess` hypotheses. Other obligations need manual specs or extra hyps.
  - **Composite specs**: Multi-instruction sub-specs (e.g., `add_limb_carry_spec`)
    can't be auto-resolved. Use manual mode: `runBlock s1 s2`.
-/

import Lean
import EvmAsm.Tactics.SeqFrame
import EvmAsm.Tactics.SpecDb

open Lean Meta Elab Tactic

initialize registerTraceClass `runBlock

namespace EvmAsm.Tactics

/-- Inline all leading `let` bindings and strip metadata wrappers.
    Handles `Expr.mdata`, `Expr.letE`, and `letFun v (fun x => body)` patterns. -/
private partial def inlineLets : Expr → Expr
  | .mdata _ e => inlineLets e
  | .letE _ _ val body _ => inlineLets (body.instantiate1 val)
  | e =>
    -- Check for letFun v (fun x => body) pattern
    if e.isAppOfArity ``letFun 4 then
      let f := e.getAppArgs[3]!
      let v := e.getAppArgs[2]!
      match f with
      | .lam _ _ body _ => inlineLets (body.instantiate1 v)
      | _ => e
    else e

/-- Normalize the exit address of a cpsTriple proof to match a target address.
    Proves equality via `bv_omega` when needed. -/
private def normalizeAddr (accExpr : Expr) (targetExit : Expr) : MetaM Expr := do
  let accType ← inferType accExpr
  let some (entry, exit₁, P, Q) ← parseCpsTriple? accType
    | throwError "runBlock: not a cpsTriple"
  if ← withoutModifyingState (isDefEq exit₁ targetExit) then
    return accExpr
  let eqType ← mkEq exit₁ targetExit
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic eqMVar.mvarId! stx
  catch _ =>
    throwError "runBlock: cannot prove address equality:\n  {exit₁} = {targetExit}"
  let eqProof ← instantiateMVars eqMVar
  let addrType ← inferType exit₁
  withLocalDeclD `x addrType fun x => do
    let body := mkAppN (mkConst ``EvmAsm.cpsTriple) #[entry, x, P, Q]
    let motive ← mkLambdaFVars #[x] body
    let congrProof ← mkCongrArg motive eqProof
    mkEqMP congrProof accExpr

/-- Frame the first spec against the goal precondition and permute.
    Given s1 : cpsTriple entry exit P1 Q1 and goalPre (the goal's precondition),
    returns : cpsTriple entry exit goalPre (Q1 ** Frame) where Frame = goalPre \ P1. -/
private def frameFirstSpec (s1Expr : Expr) (goalPre : Expr) : MetaM Expr := do
  let s1Type ← inferType s1Expr
  let some (entry, exit_, preP1, postQ1) ← parseCpsTriple? s1Type
    | throwError "runBlock: first spec is not a cpsTriple"
  -- Compute frame: goalPre atoms not in P1
  let frameAtoms ← computeFrame goalPre preP1
  if frameAtoms.isEmpty then
    -- No frame needed, just permute precondition
    -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
    -- P = preP1 (from s1), P' = goalPre (what we want), hpre : goalPre → preP1
    let prePermProof ← mkPermLambda goalPre preP1
    let postIdProof ← mkIdLambda postQ1
    return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
      #[entry, exit_, preP1, goalPre, postQ1, postQ1, prePermProof, postIdProof, s1Expr]
  -- Build frame expression
  let frameExpr ← buildSepConjChain frameAtoms
  -- Prove pcFree for the frame
  let pcFreeType := mkApp (mkConst ``EvmAsm.Assertion.pcFree) frameExpr
  let pcFreeMVar ← mkFreshExprMVar pcFreeType
  try
    let stx ← `(tactic| pcFree)
    let _ ← Lean.Elab.runTactic pcFreeMVar.mvarId! stx
  catch _ =>
    throwError "runBlock: could not prove pcFree for initial frame:\n  {frameExpr}"
  let pcFreeProof ← instantiateMVars pcFreeMVar
  -- Frame s1: cpsTriple entry exit (P1 ** F) (Q1 ** F)
  let s1Framed := mkAppN (mkConst ``EvmAsm.cpsTriple_frame_left)
    #[entry, exit_, preP1, postQ1, frameExpr, pcFreeProof, s1Expr]
  -- Permute precondition: goalPre → (P1 ** F)
  let p1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) preP1 frameExpr
  -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
  -- P = p1StarFrame (from s1Framed), P' = goalPre, hpre : goalPre → p1StarFrame
  let prePermProof ← mkPermLambda goalPre p1StarFrame
  let q1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) postQ1 frameExpr
  let postIdProof ← mkIdLambda q1StarFrame
  return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[entry, exit_, p1StarFrame, goalPre, q1StarFrame, q1StarFrame,
      prePermProof, postIdProof, s1Framed]

/-- Core: compose an array of cpsTriple proofs with initial framing,
    address normalization, and seqFrame chaining. -/
private def runBlockCore (specs : Array Expr) (goalPre : Expr) : MetaM Expr := do
  if specs.size == 0 then
    throwError "runBlock: no specs provided.\n\
        Usage: `runBlock s1 s2 ...` (manual) or `runBlock` (auto from @[spec_gen] database)."
  -- Frame the first spec against the goal precondition
  let mut acc ← frameFirstSpec specs[0]! goalPre
  -- Chain remaining specs via seqFrame with address normalization
  for i in [1:specs.size] do
    let nextSpec := specs[i]!
    let nextType ← inferType nextSpec
    let some (nextEntry, _, _, _) ← parseCpsTriple? nextType
      | throwError "runBlock: argument {i + 1} is not a cpsTriple"
    acc ← normalizeAddr acc nextEntry
    acc ← seqFrameCore acc nextSpec
  return acc

/-- Try to normalize a cpsTriple's exit to match the goal's exit address. -/
private def normalizeToGoal (composed : Expr) (goalType : Expr) : MetaM Expr := do
  if let some (_, goalExit, _, _) ← parseCpsTriple? goalType then
    try return ← normalizeAddr composed goalExit catch _ => return composed
  return composed

-- ============================================================================
-- Section: Auto-resolution of specs from precondition
-- ============================================================================

/-- Check if an expression's head is a constructor. -/
private def isCtorApp (env : Environment) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const name _ => env.isConstructor name
  | _ => false

/-- Check if a type is a decidable proposition about concrete values
    (e.g., `Reg.x7 ≠ Reg.x0`). -/
private def isConcreteDecidable (ty : Expr) : MetaM Bool := do
  if ty.isAppOfArity ``Ne 3 then
    let env ← getEnv
    let args := ty.getAppArgs
    return isCtorApp env args[1]! && isCtorApp env args[2]!
  return false

/-- Try to solve a proof obligation MVar.
    Uses mkDecideProof for concrete decidable props (register inequalities),
    local context search for hypotheses, and bv_omega as fallback. -/
private def solveObligation (mvarId : MVarId) : MetaM Bool := do
  let ty ← instantiateMVars (← mvarId.getType)
  -- Try Decidable proof for concrete propositions (rd ≠ .x0, rd ≠ rs, etc.)
  if ← isConcreteDecidable ty then
    try
      let proof ← mkDecideProof ty
      mvarId.assign proof
      return true
    catch _ =>
      (Pure.pure PUnit.unit : MetaM PUnit)
  -- Try searching local context (handles isValidMemAccess from hypotheses)
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type ty then
        mvarId.assign decl.toExpr
        return true
  -- Try bv_omega as last resort
  try
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic mvarId stx
    return true
  catch _ =>
    return false

/-- Try to instantiate a single spec theorem for a given instruction and state.
    Uses unification: creates MVars for all spec parameters, unifies the spec's
    instruction and register/memory atoms with the state, then solves proof
    obligations. Returns the instantiated proof term. -/
private def tryInstantiateSpec (specName : Name) (instrExpr instrAddr : Expr)
    (stateAtoms : List Expr) : MetaM Expr := do
  let specConst := mkConst specName
  let specType ← inferType specConst
  -- Create metavariable telescope for spec parameters (non-reducing to avoid
  -- unfolding cpsTriple, which is itself a ∀ internally)
  let (params, _, body) ← forallMetaTelescope specType
  -- body should be cpsTriple entry exit pre post
  let some (specEntry, _, specPre, _) ← parseCpsTriple? body
    | throwError "tryInstantiateSpec: {specName} is not a cpsTriple"
  -- Step 1: Unify spec address with our instruction address
  unless ← isDefEq specEntry instrAddr do
    throwError "address mismatch"
  -- Step 2: Flatten spec precondition and match atoms
  let specAtoms ← flattenSepConj specPre
  -- Step 2a: Unify the instrAt atom
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.instrAt 2 then
      let specInstr := atom.getAppArgs[1]!
      unless ← isDefEq specInstr instrExpr do
        throwError "instruction mismatch"
  -- Step 2b: Unify regIs atoms
  let stateRegAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.regIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.regIs 2 then
      let specReg ← instantiateMVars atom.getAppArgs[0]!
      let specVal := atom.getAppArgs[1]!
      let mut found := false
      for stateAtom in stateRegAtoms do
        let stateReg := stateAtom.getAppArgs[0]!
        let stateVal := stateAtom.getAppArgs[1]!
        if ← withoutModifyingState (isDefEq specReg stateReg) then
          let _ ← isDefEq specReg stateReg
          let _ ← isDefEq specVal stateVal
          found := true
          break
      unless found do
        throwError "register {specReg} not found in state"
  -- Step 2c: Unify memIs atoms
  let stateMemAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.memIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.memIs 2 then
      let specAddr ← instantiateMVars atom.getAppArgs[0]!
      let specVal := atom.getAppArgs[1]!
      let mut found := false
      for stateAtom in stateMemAtoms do
        let stateAddr := stateAtom.getAppArgs[0]!
        let stateVal := stateAtom.getAppArgs[1]!
        if ← withoutModifyingState (isDefEq specAddr stateAddr) then
          let _ ← isDefEq specAddr stateAddr
          let _ ← isDefEq specVal stateVal
          found := true
          break
      unless found do
        throwError "memory at {specAddr} not found in state"
  -- Step 3: Solve remaining proof obligations
  for param in params do
    if !param.isMVar then continue
    let mvarId := param.mvarId!
    if ← mvarId.isAssigned then continue
    let solved ← solveObligation mvarId
    unless solved do
      let paramType ← instantiateMVars (← mvarId.getType)
      throwError "cannot solve proof obligation: {paramType}\n\
          Hint: Add the obligation as a hypothesis to the theorem, or use manual mode."
  -- Build fully instantiated application
  return ← instantiateMVars (mkAppN specConst params)

/-- Resolve a spec for an instruction by trying all registered specs.
    Returns the first successfully instantiated spec proof. -/
private def resolveSpecForInstr (instrExpr instrAddr : Expr)
    (stateAtoms : List Expr) : MetaM Expr := do
  let instrHead := instrExpr.getAppFn
  let .const instrName _ := instrHead
    | throwError "runBlock: instruction is not a constructor application: {instrExpr}\n\
        Hint: All instructions in the precondition must be concrete (e.g., `.ADD .x7 .x7 .x6`)."
  let env ← getEnv
  let specs := findSpecsForInstr env instrName
  if specs.isEmpty then
    throwError "runBlock: no @[spec_gen] specs registered for `{instrName}`.\n\
        Hint: Add `@[spec_gen]` to a theorem with `{instrName}` in its precondition,\n\
        or use manual mode: `runBlock s1 s2 ...`.\n\
        Use `#spec_db` to see all registered specs."
  trace[runBlock] "resolving {instrName} at {instrAddr} — {specs.size} candidate(s)"
  let mut errors : Array (Name × String) := #[]
  for entry in specs do
    let saved ← saveState
    try
      let result ← tryInstantiateSpec entry.specName instrExpr instrAddr stateAtoms
      trace[runBlock] "  resolved with {entry.specName}"
      return result
    catch e =>
      restoreState saved
      let msg := toString (← e.toMessageData.format)
      errors := errors.push (entry.specName, msg)
      continue
  -- Build detailed error with all attempted specs
  let mut errMsg := m!"runBlock: no spec could be instantiated for `{instrName}` at {instrAddr}."
  errMsg := errMsg ++ m!"\n  Tried {errors.size} candidate(s):"
  for (name, msg) in errors do
    errMsg := errMsg ++ m!"\n    {name}: {msg}"
  errMsg := errMsg ++ m!"\n  Hint: Use `set_option trace.runBlock true` for detailed resolution output."
  throwError errMsg

/-- Compute the state atoms after applying a resolved spec.
    Returns postcondition atoms ∪ (currentAtoms \ precondition atoms). -/
private def advanceState (currentAtoms : List Expr) (specExpr : Expr) : MetaM (List Expr) := do
  let specType ← inferType specExpr
  let some (_, _, specPre, specPost) ← parseCpsTriple? specType
    | throwError "advanceState: not a cpsTriple"
  let preAtoms ← flattenSepConj specPre
  let postAtoms ← flattenSepConj specPost
  -- Remove consumed atoms (those in spec's precondition)
  let mut available := currentAtoms.toArray.map fun a => (a, true)
  for preAtom in preAtoms do
    for i in [:available.size] do
      if available[i]!.2 then
        if ← withReducible (isDefEq preAtom available[i]!.1) then
          available := available.set! i (available[i]!.1, false)
          break
  let frame := available.filter (·.2) |>.map (·.1) |>.toList
  return postAtoms ++ frame

/-- Extract instruction atoms `(addr, instrExpr)` from assertion atoms,
    preserving the order they appear in the precondition. -/
private def extractInstrAtoms (atoms : List Expr) : List (Expr × Expr) :=
  atoms.filterMap fun atom =>
    if atom.isAppOfArity `EvmAsm.instrAt 2 then
      some (atom.getAppArgs[0]!, atom.getAppArgs[1]!)
    else none

/-- Auto-resolve all specs from the precondition and compose them.
    Extracts instruction atoms, resolves each spec using the current state,
    and advances the state between instructions. -/
private def autoResolveAndCompose (goalPre : Expr) : MetaM Expr := do
  let atoms ← flattenSepConj goalPre
  let instrAtoms := extractInstrAtoms atoms
  if instrAtoms.isEmpty then
    throwError "runBlock: no `instrAt` (↦ᵢ) atoms found in the goal's precondition.\n\
        The goal must be a `cpsTriple` whose precondition contains instruction atoms."
  -- Non-instruction atoms form the initial state
  let stateAtoms := atoms.filter fun a => !a.isAppOfArity `EvmAsm.instrAt 2
  trace[runBlock] "auto mode: {instrAtoms.length} instruction(s), {stateAtoms.length} state atom(s)"
  let mut currentState := stateAtoms
  let mut specs : Array Expr := #[]
  let mut resolvedCount : Nat := 0
  let totalCount := instrAtoms.length
  for (addr, instr) in instrAtoms do
    try
      let spec ← resolveSpecForInstr instr addr currentState
      specs := specs.push spec
      currentState ← advanceState currentState spec
      resolvedCount := resolvedCount + 1
    catch e =>
      -- Re-throw with progress context
      let eMsg ← e.toMessageData.format
      throwError "{eMsg}\n  Progress: resolved {resolvedCount} of {totalCount} instruction(s) before failure."
  trace[runBlock] "all {specs.size} spec(s) resolved, composing..."
  runBlockCore specs goalPre

/-- Verify a basic block by composing instruction specs with automatic framing.

    **Auto mode** (no arguments): resolves specs from the `@[spec_gen]` database.
    ```
    runBlock
    ```

    **Manual mode** (with hypotheses): composes the given `cpsTriple` proofs.
    ```
    runBlock s1 s2 s3
    ```

    The goal must be a `cpsTriple entry exit pre post`. In auto mode, the
    precondition must contain `instrAt` (`↦ᵢ`) atoms for each instruction.

    **Debugging**: use `set_option trace.runBlock true` to see resolution details. -/
elab "runBlock" specs:ident* : tactic => withMainContext do
  let goal ← getMainGoal
  -- Strip leading let bindings and metadata from goal type
  let goalType := inlineLets (← instantiateMVars (← goal.getType))
  let some (_, _, goalPre, _) ← parseCpsTriple? goalType
    | throwError "runBlock: goal is not a `cpsTriple`.\n\
        Expected goal of the form: `cpsTriple entry exit pre post`."
  let composed ←
    if specs.isEmpty then
      -- Auto mode: resolve specs from precondition
      autoResolveAndCompose goalPre
    else
      -- Manual mode: use provided specs
      let specExprs ← specs.mapM fun s => elabTerm s none
      runBlockCore specExprs goalPre
  let finalResult ← normalizeToGoal composed goalType
  -- Always permute postcondition to match goal (goal.assign doesn't type-check)
  let some (gEntry, gExit, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "runBlock: internal error — goal lost cpsTriple structure during permutation"
  let resultType ← inferType finalResult
  let some (_, _, _, resultPost) ← parseCpsTriple? resultType
    | throwError "runBlock: internal error — composed result is not a cpsTriple"
  -- cpsTriple_consequence (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
  -- P = gPre (what finalResult has), P' = gPre (same, identity), Q = resultPost, Q' = goalPost
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  let permuted := mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[gEntry, gExit, gPre, gPre, resultPost, goalPost, idPre, postPerm, finalResult]
  goal.assign permuted
  replaceMainGoal []

end EvmAsm.Tactics
