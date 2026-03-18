/-
  EvmAsm.Rv32.Tactics.RunBlock

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
import EvmAsm.Rv32.Tactics.SeqFrame
import EvmAsm.Rv32.Tactics.SpecDb

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

-- ============================================================================
-- Section: CodeReq Extension (from SeqFrame)
-- ============================================================================

/-- Build identity monotonicity proof: fun a i h => h -/
private def mkIdentityMono (cr : Expr) : MetaM Expr := do
  let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
  let instrType := mkConst ``EvmAsm.Instr
  withLocalDeclD `a bv32 fun a =>
    withLocalDeclD `i instrType fun i => do
      let someI ← mkAppOptM ``some #[instrType, i]
      let eqType ← mkEq (mkApp cr a) someI
      withLocalDeclD `h eqType fun h =>
        mkLambdaFVars #[a, i, h] h

/-- Fallback: Build monotonicity proof via tactic (for edge cases). -/
private def buildMonoProofTactic (oldCr newCr : Expr) : MetaM Expr := do
  let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
  let instrType := mkConst ``EvmAsm.Instr
  let propType ← withLocalDeclD `a bv32 fun a => do
    withLocalDeclD `i instrType fun i => do
      let oldCrA := mkApp oldCr a
      let newCrA := mkApp newCr a
      let someI ← mkAppOptM ``some #[instrType, i]
      let ant ← mkEq oldCrA someI
      let cons ← mkEq newCrA someI
      let body ← mkArrow ant cons
      let body' ← mkForallFVars #[i] body
      mkForallFVars #[a] body'
  let mvar ← mkFreshExprMVar propType
  let saved ← saveState
  try
    let stx ← `(tactic| intro a i h; simp only [EvmAsm.CodeReq.singleton, EvmAsm.CodeReq.union] at *; (first | simp_all | (split at h <;> simp_all <;> bv_omega)))
    let _ ← Lean.Elab.runTactic mvar.mvarId! stx
    return ← instantiateMVars mvar
  catch _ => restoreState saved
  throwError "runBlock: cannot build monotonicity proof for CodeReq extension (fallback)"

/-- Build a proof of `∀ a i, oldCr a = some i → newCr a = some i` structurally.
    Walks the union chain to find matching pieces, composing with
    CodeReq.union_mono_left, mono_union_right, and union_split_mono.
    Falls back to tactic-based proof for edge cases. -/
private partial def buildMonoProof (oldCr newCr : Expr) : MetaM Expr := do
  -- Identity: oldCr ≡ newCr (structural check first, then isDefEq fallback)
  if oldCr == newCr then
    return ← mkIdentityMono oldCr
  if ← withoutModifyingState (withReducible (isDefEq oldCr newCr)) then
    return ← mkIdentityMono oldCr
  let oldCrW ← whnfR oldCr
  let newCrW ← whnfR newCr
  -- oldCr = union(sub1, sub2): split and recurse
  if oldCrW.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let sub1 := oldCrW.getAppArgs[0]!
    let sub2 := oldCrW.getAppArgs[1]!
    let headMono ← buildMonoProof sub1 newCr
    let tailMono ← buildMonoProof sub2 newCr
    return ← mkAppM ``EvmAsm.CodeReq.union_split_mono #[headMono, tailMono]
  -- newCr = union(head, tail): walk the chain
  if newCrW.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let head := newCrW.getAppArgs[0]!
    let tail := newCrW.getAppArgs[1]!
    -- Left match: oldCr ≡ head (structural check first)
    if oldCr == head then
      return ← mkAppM ``EvmAsm.CodeReq.union_mono_left #[head, tail]
    if ← withoutModifyingState (withReducible (isDefEq oldCr head)) then
      return ← mkAppM ``EvmAsm.CodeReq.union_mono_left #[head, tail]
    -- Skip: prove head.Disjoint oldCr, recurse on tail
    let disjProof ← buildDisjointProof head oldCr
    let tailMono ← buildMonoProof oldCr tail
    return ← mkAppM ``EvmAsm.CodeReq.mono_union_right #[disjProof, tailMono]
  -- Fallback: tactic-based proof
  buildMonoProofTactic oldCr newCr

/-- Extend a spec's CodeReq from oldCr to newCr using `cpsTriple_extend_code`. -/
private def extendSpecCr (spec : Expr) (oldCr newCr : Expr) : MetaM Expr := do
  if oldCr == newCr then return spec
  if ← withoutModifyingState (withReducible (isDefEq oldCr newCr)) then
    return spec
  let monoProof ← buildMonoProof oldCr newCr
  mkAppM ``EvmAsm.cpsTriple_extend_code #[monoProof, spec]

-- ============================================================================
-- Section: Address Normalization for Sub-Spec Composition
-- ============================================================================

/-- Check if an expression is a numeric literal (OfNat.ofNat _ n _) and return n. -/
private def getBvLitVal? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getAppArgs[1]! with
    | .lit (.natVal n) => some n
    | _ => none
  else none

/-- Prove `old = new` via `bv_omega`. Returns `none` on failure.
    Tries `mkDecideProof` first (fast for concrete BitVec equalities),
    then falls back to `bv_omega` via `runTactic`. -/
private def proveBvEq (old new_ : Expr) : MetaM (Option Expr) := do
  if old == new_ then return some (← mkEqRefl old)
  if ← withoutModifyingState (isDefEq old new_) then
    return some (← mkEqRefl old)
  let eqType ← mkEq old new_
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic eqMVar.mvarId! stx
    return some (← instantiateMVars eqMVar)
  catch _ => return none

/-- Prove `old = new` for concrete decidable propositions.
    Uses `mkDecideProof` (no tactic overhead). Falls back to `native_decide` via `runTactic`. -/
private def proveByNativeDecide (old new_ : Expr) : MetaM (Option Expr) := do
  let eqType ← mkEq old new_
  -- Try mkDecideProof (fast path, avoids runTactic overhead)
  try return some (← mkDecideProof eqType)
  catch _ => (Pure.pure PUnit.unit : MetaM PUnit)
  -- Fallback to native_decide
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| native_decide)
    let _ ← Lean.Elab.runTactic eqMVar.mvarId! stx
    return some (← instantiateMVars eqMVar)
  catch _ => return none

/-- Try to simplify a fully-recursed expression at the top level:
    - `signExtend12 N` (concrete N) → numeric literal
    - `e + 0` → `e`
    - `(a + lit₁) + lit₂` → `a + (lit₁ + lit₂)` -/
private def trySimplifyTop (e : Expr) : MetaM (Expr × Option Expr) := do
  -- signExtend12 on concrete literal
  if e.isAppOfArity ``EvmAsm.signExtend12 1 then
    let arg := e.getAppArgs[0]!
    if let some argVal := getBvLitVal? arg then
      let n12 := argVal % 4096
      let signExtVal := if n12 < 2048 then n12 else n12 + (2^32 - 4096)
      let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
      let resultExpr ← mkNumeral bv32 signExtVal
      -- Use native_decide tactic (avoids deep kernel reduction that
      -- mkDecideProof triggers for signExtend12)
      let eqType ← mkEq e resultExpr
      let eqMVar ← mkFreshExprMVar eqType
      try
        let stx ← `(tactic| native_decide)
        let _ ← Lean.Elab.runTactic eqMVar.mvarId! stx
        return (resultExpr, some (← instantiateMVars eqMVar))
      catch _ => (Pure.pure PUnit.unit : MetaM PUnit)
  -- Address arithmetic at BitVec type
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let args := e.getAppArgs
    let lhs := args[4]!
    let rhs := args[5]!
    let eTy ← inferType e
    if (← whnf eTy).isAppOfArity ``BitVec 1 then
      -- e + 0 → e
      if getBvLitVal? rhs == some 0 then
        if let some pf ← proveBvEq e lhs then
          return (lhs, some pf)
      -- (a + lit₁) + lit₂ → a + (lit₁ + lit₂)
      if let some rhsVal := getBvLitVal? rhs then
        if lhs.isAppOfArity ``HAdd.hAdd 6 then
          let lhsArgs := lhs.getAppArgs
          let b := lhsArgs[5]!
          if let some bVal := getBvLitVal? b then
            let a := lhsArgs[4]!
            let bv32 := mkApp (mkConst ``BitVec) (mkNatLit 32)
            let sumLit ← mkNumeral bv32 (bVal + rhsVal)
            let result ← mkAppM ``HAdd.hAdd #[a, sumLit]
            if let some pf ← proveBvEq e result then
              return (result, some pf)
  return (e, none)

/-- Bottom-up normalization walk on a cpsTriple type expression.
    First recurses into `.app` sub-expressions, then tries top-level simplifications.
    This ensures `signExtend12 0` is reduced to `0` before `sp + 0 → sp` is checked.

    Returns (normalized_expr, proof : original = normalized) or (original, none). -/
partial def normalizeTypeAddrs (e : Expr) : MetaM (Expr × Option Expr) := do
  -- Fast exit: atoms that never contain address arithmetic
  if e.isConst || e.isFVar || e.isLit || e.isBVar || e.isSort then return (e, none)
  -- Fast exit: constructor applications (register/instruction constructors, etc.)
  if let .const name _ := e.getAppFn then
    let env ← getEnv
    if env.isConstructor name then return (e, none)
    -- OfNat.ofNat wraps numeric literals — no address arithmetic inside
    if name == ``OfNat.ofNat then return (e, none)
    -- ite/dite have dependent types — congruence proofs fail, skip them
    if name == ``ite || name == ``dite then return (e, none)
    -- BitVec.ult and similar comparison functions — no address arithmetic
    if name == ``BitVec.ult then return (e, none)
  -- Fast exit: implicit type/instance arguments (avoid recursing into HAdd instances, etc.)
  -- Check if the expression's type is Type/Sort (not data-level)
  if let .const name _ := e.getAppFn then
    if name == ``HAdd.hAdd || name == ``HSub.hSub || name == ``HMul.hMul ||
       name == ``HShiftLeft.hShiftLeft || name == ``HShiftRight.hShiftRight ||
       name == ``HAnd.hAnd || name == ``HOr.hOr || name == ``HXor.hXor then
      -- Only recurse into last 2 args (operands), skip type/instance args
      if e.getAppNumArgs >= 2 then
        let args := e.getAppArgs
        let n := args.size
        let (lhs', lhsPf?) ← normalizeTypeAddrs args[n - 2]!
        let (rhs', rhsPf?) ← normalizeTypeAddrs args[n - 1]!
        if lhsPf?.isNone && rhsPf?.isNone then
          -- No changes in operands, just try top-level simplification
          let (e'', topPf?) ← trySimplifyTop e
          return match topPf? with
          | some _ => (e'', topPf?)
          | none => (e, none)
        else
          let argsNew := args.set! (n - 2) lhs' |>.set! (n - 1) rhs'
          let new_ := mkAppN e.getAppFn argsNew
          let pf? ← try
            let pf ← match lhsPf?, rhsPf? with
              | some lPf, some rPf =>
                let fFull := mkAppN e.getAppFn (args[:n-2].toArray)
                let feq ← mkCongrArg fFull lPf
                mkCongr (← mkCongrFun feq args[n-1]!) rPf
              | some lPf, none =>
                let fFull := mkAppN e.getAppFn (args[:n-2].toArray)
                mkCongrFun (← mkCongrArg fFull lPf) args[n-1]!
              | none, some rPf =>
                let fPartial := mkAppN e.getAppFn (args[:n-1].toArray)
                mkCongrArg fPartial rPf
              | none, none => unreachable!
            Pure.pure (some pf)
          catch _ => Pure.pure none
          let (e'', topPf?) ← trySimplifyTop new_
          match pf?, topPf? with
          | none, none => return (e, none)
          | some cp, none => return (new_, some cp)
          | none, some tp => return (e'', some tp)
          | some cp, some tp => return (e'', some (← mkEqTrans cp tp))
  -- 1. Recurse into .app sub-expressions first (bottom-up)
  let (e', childPf?) ← match e with
    | .app f a => do
      let (f', fPf?) ← normalizeTypeAddrs f
      let (a', aPf?) ← normalizeTypeAddrs a
      if fPf?.isNone && aPf?.isNone then Pure.pure (e, none)
      else
        let new_ := Expr.app f' a'
        -- Build congruence proof; catch failures for dependent types (e.g., ite/Decidable)
        try
          let pf ← match fPf?, aPf? with
            | some fPf, some aPf => mkCongr fPf aPf
            | some fPf, none => mkCongrFun fPf a
            | none, some aPf => mkCongrArg f aPf
            | none, none => unreachable!
          Pure.pure (new_, some pf)
        catch _ =>
          -- Can't build congruence (dependent type) — return unchanged
          Pure.pure (e, none)
    | _ => Pure.pure (e, none)
  -- 2. Try top-level simplifications on the (possibly modified) expression
  let (e'', topPf?) ← trySimplifyTop e'
  -- 3. If top-level simplified, try again (e.g., after (a+b)+c → a+(b+c), check a+(b+c)+0)
  let (final, finalPf?) ← if topPf?.isSome then do
    let (e''', morePf?) ← trySimplifyTop e''
    match morePf? with
    | some mp => Pure.pure (e''', some (← mkEqTrans topPf?.get! mp))
    | none => Pure.pure (e'', topPf?)
  else Pure.pure (e'', topPf?)
  -- 4. Combine child and top-level proofs
  match childPf?, finalPf? with
  | none, none => Pure.pure (e, none)
  | some cp, none => Pure.pure (e', some cp)
  | none, some tp => Pure.pure (final, some tp)
  | some cp, some tp => Pure.pure (final, some (← mkEqTrans cp tp))

/-- Normalize addresses in a single assertion atom (e.g., `regIs .x12 (sp + signExtend12 32)`
    → `regIs .x12 (sp + 32)`). Returns the normalized expression.
    Used by `advanceState` to keep state atoms in normalized form. -/
private def normalizeAtomAddrs (e : Expr) : MetaM Expr := do
  let (e', _) ← normalizeTypeAddrs e
  return e'

/-- Normalize addresses in a cpsTriple proof.
    First inlines `let` bindings (which are definitionally equal),
    then eliminates `signExtend12 N` for concrete N and flattens address arithmetic
    `(base + N) + M` → `base + (N+M)` and `e + 0` → `e`.
    Transports the original proof via `Eq.mp` (works because cpsTriple is Prop-valued). -/
private def normalizeSpecAddresses (proof : Expr) : MetaM Expr := do
  let origType ← instantiateMVars (← inferType proof)
  -- Inline let-bindings first (e.g., `let mem := sp + signExtend12 off; ...`)
  let cleanType := inlineLets origType
  let (_, normPf?) ← normalizeTypeAddrs cleanType
  match normPf? with
  | some pf => mkEqMP pf proof
  | none =>
    -- If let-inlining changed the type shape, wrap with @id to force the clean type
    -- (let-inlined type is definitionally equal, so the kernel accepts it)
    if cleanType == origType then Pure.pure proof
    else Pure.pure (mkApp2 (mkConst ``id [levelZero]) cleanType proof)

/-- Normalize the exit address of a cpsTriple proof to match a target address.
    Proves equality via `bv_omega` when needed. -/
private def normalizeAddr (accExpr : Expr) (targetExit : Expr) : MetaM Expr := do
  let accType ← inferType accExpr
  let some (entry, exit₁, cr, P, Q) ← parseCpsTriple? accType
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
    let body := mkAppN (mkConst ``EvmAsm.cpsTriple) #[entry, x, cr, P, Q]
    let motive ← mkLambdaFVars #[x] body
    let congrProof ← mkCongrArg motive eqProof
    mkEqMP congrProof accExpr

/-- Frame the first spec against the goal precondition and permute.
    Given s1 : cpsTriple entry exit cr P1 Q1 and goalPre (the goal's precondition),
    returns : cpsTriple entry exit cr goalPre (Q1 ** Frame) where Frame = goalPre \ P1. -/
private def frameFirstSpec (s1Expr : Expr) (goalPre : Expr) : MetaM Expr := do
  let s1Type ← inferType s1Expr
  let some (entry, exit_, cr, preP1, postQ1) ← parseCpsTriple? s1Type
    | throwError "runBlock: first spec is not a cpsTriple"
  -- Compute frame: goalPre atoms not in P1
  let frameAtoms ← computeFrame goalPre preP1
  if frameAtoms.isEmpty then
    -- No frame needed, just permute precondition
    -- cpsTriple_consequence (entry exit_ cr P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple entry exit_ cr P Q) : cpsTriple entry exit_ cr P' Q'
    -- P = preP1 (from s1), P' = goalPre (what we want), hpre : goalPre → preP1
    let prePermProof ← mkPermLambda goalPre preP1
    let postIdProof ← mkIdLambda postQ1
    return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
      #[entry, exit_, cr, preP1, goalPre, postQ1, postQ1, prePermProof, postIdProof, s1Expr]
  -- Build frame expression
  let frameExpr ← buildSepConjChain frameAtoms
  -- Prove pcFree for the frame (direct proof construction, no tactic overhead)
  let pcFreeProof ← try buildPcFreeProof frameExpr
    catch _ => throwError "runBlock: could not prove pcFree for initial frame:\n  {frameExpr}"
  -- Frame s1: cpsTriple entry exit_ cr (P1 ** F) (Q1 ** F)
  let s1Framed := mkAppN (mkConst ``EvmAsm.cpsTriple_frame_left)
    #[entry, exit_, cr, preP1, postQ1, frameExpr, pcFreeProof, s1Expr]
  -- Permute precondition: goalPre → (P1 ** F)
  let p1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) preP1 frameExpr
  -- cpsTriple_consequence (entry exit_ cr P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple entry exit_ cr P Q) : cpsTriple entry exit_ cr P' Q'
  -- P = p1StarFrame (from s1Framed), P' = goalPre, hpre : goalPre → p1StarFrame
  let prePermProof ← mkPermLambda goalPre p1StarFrame
  let q1StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) postQ1 frameExpr
  let postIdProof ← mkIdLambda q1StarFrame
  return mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[entry, exit_, cr, p1StarFrame, goalPre, q1StarFrame, q1StarFrame,
      prePermProof, postIdProof, s1Framed]

/-- Core: compose an array of cpsTriple proofs with initial framing,
    address normalization, and seqFrame chaining.
    When `normalizeAddrs` is true (manual mode), applies signExtend12 reduction
    and address arithmetic flattening to each spec before composing. -/
private def runBlockCore (specs : Array Expr) (goalPre : Expr) (goalCr : Expr)
    (normalizeAddrs : Bool := false) : MetaM Expr := do
  if specs.size == 0 then
    throwError "runBlock: no specs provided.\n\
        Usage: `runBlock s1 s2 ...` (manual) or `runBlock` (auto from @[spec_gen] database)."
  -- Normalize addresses in manual-mode specs (signExtend12, address flattening)
  let processedSpecs ← if normalizeAddrs then
    specs.mapM fun spec => do
      try normalizeSpecAddresses spec
      catch _ => Pure.pure spec
  else Pure.pure specs
  -- Extend each spec to goalCr
  let extendToGoal := fun spec => do
    let specType ← instantiateMVars (← inferType spec)
    let some (_, _, specCr, _, _) ← parseCpsTriple? specType | throwError "runBlockCore: not cpsTriple"
    extendSpecCr spec specCr goalCr
  trace[runBlock] "extending {processedSpecs.size} spec(s) to goalCr..."
  let extendedSpecs ← processedSpecs.mapM extendToGoal
  trace[runBlock] "all spec(s) extended, composing..."
  -- Frame the first spec against the goal precondition
  let mut acc ← frameFirstSpec extendedSpecs[0]! goalPre
  -- Chain remaining specs
  -- Chain remaining specs via seqFrame with address normalization
  for i in [1:extendedSpecs.size] do
    let nextSpec := extendedSpecs[i]!
    let nextType ← inferType nextSpec
    let some (nextEntry, _, _, _, _) ← parseCpsTriple? nextType
      | throwError "runBlock: argument {i + 1} is not a cpsTriple"
    acc ← normalizeAddr acc nextEntry
    acc ← seqFrameCore acc nextSpec
  return acc

/-- Try to normalize a cpsTriple's exit to match the goal's exit address. -/
private def normalizeToGoal (composed : Expr) (goalType : Expr) : MetaM Expr := do
  if let some (_, goalExit, _, _, _) ← parseCpsTriple? goalType then
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

/-- Extract the target address from `isValidMemAccess target = true`. -/
private def parseIsValidMemAccess? (ty : Expr) : MetaM (Option Expr) := do
  -- ty should be `@BEq.beq Bool _ (isValidMemAccess target) true = true`
  -- or `isValidMemAccess target = true` (Eq Bool (isValidMemAccess target) true)
  if !ty.isAppOfArity ``Eq 3 then return none
  let args := ty.getAppArgs
  -- args[1] = lhs, args[2] = rhs (= true)
  let lhs := args[1]!
  let rhs := args[2]!
  -- rhs should be `true`
  unless rhs == mkConst ``Bool.true do return none
  -- lhs should be `isValidMemAccess target`
  if lhs.isAppOfArity ``EvmAsm.isValidMemAccess 1 then
    return some lhs.getAppArgs[0]!
  return none

/-- Get a Nat literal value from an expression (handles raw `.lit` and `OfNat.ofNat`). -/
private def getNatLitVal? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getAppArgs[1]! with
      | .lit (.natVal n) => some n
      | _ => none
    else none

/-- Try to extract a concrete byte offset from `target` relative to `validAddr`.
    Handles: `validAddr` (offset 0), `validAddr + lit`, `validAddr + signExtend12 lit`. -/
private def extractConcreteOffset? (validAddr target : Expr) : MetaM (Option Nat) := do
  -- Case 1: target = validAddr (offset 0)
  if ← withoutModifyingState (isDefEq validAddr target) then return some 0
  -- Case 2: target = something + rhs
  if target.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := target.getAppArgs[4]!
    let rhs := target.getAppArgs[5]!
    if ← withoutModifyingState (isDefEq validAddr lhs) then
      -- rhs is a numeric literal
      if let some v := getBvLitVal? rhs then return some v
      -- rhs is signExtend12 N
      if rhs.isAppOfArity ``EvmAsm.signExtend12 1 then
        let arg := rhs.getAppArgs[0]!
        if let some argVal := getBvLitVal? arg then
          let n12 := argVal % 4096
          return some (if n12 < 2048 then n12 else n12 + (2^32 - 4096))
  return none

/-- Build a proof of `ValidMemRange.fetch` for a given index. -/
private def buildFetchProof (validAddr validN : Expr) (validHyp : Expr)
    (i : Nat) (nVal : Nat) (target : Expr) : MetaM (Option Expr) := do
  if i >= nVal then return none
  let fourI := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 32) (mkNatLit (4 * i))
  let indexedAddr ← mkAppM ``HAdd.hAdd #[validAddr, fourI]
  let some eqProof ← proveBvEq indexedAddr target | return none
  let iLtN ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, validN])
  return some (mkAppN (mkConst ``EvmAsm.ValidMemRange.fetch)
    #[validAddr, validN, validHyp, mkNatLit i, target, iLtN, eqProof])

/-- Try to prove `isValidMemAccess target = true` from ValidMemRange hypotheses in context.
    Fast path: extracts concrete offset from target and computes index directly.
    Slow path: tries all indices 0..n-1 with `proveBvEq`. -/
private def solveFromValidMemRange (ty : Expr) : MetaM (Option Expr) := do
  let some target ← parseIsValidMemAccess? ty | return none
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if !declType.isAppOfArity ``EvmAsm.ValidMemRange 2 then continue
    let validAddr := declType.getAppArgs[0]!
    let validN := declType.getAppArgs[1]!
    let some nVal := getNatLitVal? validN | continue
    -- Fast path: extract concrete offset and compute index directly
    if let some offset ← extractConcreteOffset? validAddr target then
      if offset % 4 == 0 then
        let i := offset / 4
        if let some proof ← buildFetchProof validAddr validN decl.toExpr i nVal target then
          return some proof
    -- Slow path: try all indices (handles complex address forms)
    for i in [:nVal] do
      let saved ← saveState
      if let some proof ← buildFetchProof validAddr validN decl.toExpr i nVal target then
        return some proof
      else
        restoreState saved
  return none

/-- Try to solve a proof obligation MVar.
    Uses mkDecideProof for concrete decidable props (register inequalities),
    local context search for hypotheses, ValidMemRange derivation, and bv_omega as fallback. -/
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
  -- Try deriving from ValidMemRange hypotheses
  if let some proof ← solveFromValidMemRange ty then
    mvarId.assign proof
    return true
  -- Try bv_omega as last resort
  try
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic mvarId stx
    return true
  catch _ =>
    return false

/-- Tactic to derive `isValidMemAccess target = true` from `ValidMemRange` in context.
    Searches for `ValidMemRange addr n` hypotheses and uses `ValidMemRange.fetch`. -/
elab "validMem" : tactic => withMainContext do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  -- Try deriving from ValidMemRange hypotheses
  if let some proof ← solveFromValidMemRange ty then
    goal.assign proof
    replaceMainGoal []
    return
  -- Fallback: search local context for matching hypothesis (handles symbolic offsets)
  let lctx ← getLCtx
  for decl in lctx do
    if !decl.isImplementationDetail then
      if ← isDefEq decl.type ty then
        goal.assign decl.toExpr
        replaceMainGoal []
        return
  throwError "validMem: could not derive from ValidMemRange or local context.\n\
      Expected goal of the form: `isValidMemAccess target = true`"

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
  -- body should be cpsTriple entry exit_ cr pre post
  let some (specEntry, _, specCr, specPre, _) ← parseCpsTriple? body
    | throwError "tryInstantiateSpec: {specName} is not a cpsTriple"
  -- Step 1: Unify spec address with our instruction address
  unless ← isDefEq specEntry instrAddr do
    throwError "address mismatch"
  -- Step 1b: Match instruction in specCr (should be CodeReq.singleton)
  -- Use whnfR (not whnf) to avoid unfolding CodeReq.singleton into a lambda
  -- Step 1b: Match instruction in specCr
  let specCrWhnf ← whnfR specCr
  if specCrWhnf.isAppOfArity ``EvmAsm.CodeReq.singleton 2 then
    let specInstr := specCrWhnf.getAppArgs[1]!
    unless ← isDefEq specInstr instrExpr do
      throwError "instruction mismatch in cr"
  -- Step 2: Flatten spec precondition and match atoms (no instrAt anymore)
  -- Step 2: Match atoms
  let specAtoms ← flattenSepConj specPre
  -- Step 2a: Unify regIs atoms
  let stateRegAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.regIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.regIs 2 then
      let specReg ← instantiateMVars atom.getAppArgs[0]!
      let specVal := atom.getAppArgs[1]!
      let mut found := false
      for stateAtom in stateRegAtoms do
        let stateReg := stateAtom.getAppArgs[0]!
        let stateVal := stateAtom.getAppArgs[1]!
        if ← withoutModifyingState (withReducible (isDefEq specReg stateReg)) then
          let _ ← isDefEq specReg stateReg
          let _ ← isDefEq specVal stateVal
          found := true
          break
      unless found do
        throwError "register {specReg} not found in state"
  -- Step 2b: Unify memIs atoms
  -- Step 2b: Match memIs atoms
  let stateMemAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.memIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.memIs 2 then
      let specAddr ← instantiateMVars atom.getAppArgs[0]!
      let specVal := atom.getAppArgs[1]!
      -- Match memory address
      -- Normalize spec address (e.g., sp + signExtend12 0 → sp,
      -- (sp + signExtend12 32) + signExtend12 4 → sp + 36)
      let specAddrNorm ← normalizeAtomAddrs specAddr
      -- Normalized
      let mut found := false
      for stateAtom in stateMemAtoms do
        let stateAddr := stateAtom.getAppArgs[0]!
        let stateVal := stateAtom.getAppArgs[1]!
        -- Try direct defEq first (fast path, reducible only to avoid deep BitVec reduction)
        if ← withoutModifyingState (withReducible (isDefEq specAddr stateAddr)) then
          let _ ← isDefEq specAddr stateAddr
          let _ ← isDefEq specVal stateVal
          found := true
          break
        -- Try normalized address (handles signExtend12 + address flattening)
        if ← withoutModifyingState (isDefEq specAddrNorm stateAddr) then
          let _ ← isDefEq specVal stateVal
          found := true
          break
      unless found do
        throwError "memory at {specAddrNorm} not found in state"
  -- Step 3: Solve proof obligations
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
  let some (_, _, _, specPre, specPost) ← parseCpsTriple? specType
    | throwError "advanceState: not a cpsTriple"
  let preAtoms ← flattenSepConj specPre
  let postAtoms ← flattenSepConj specPost
  -- Normalize postcondition atoms (e.g., signExtend12 reduction, address flattening)
  let postAtomsNorm ← postAtoms.mapM normalizeAtomAddrs
  -- Remove consumed atoms (those in spec's precondition)
  let mut available := currentAtoms.toArray.map fun a => (a, true)
  for preAtom in preAtoms do
    let preAtomNorm ← normalizeAtomAddrs preAtom
    for i in [:available.size] do
      if available[i]!.2 then
        if ← withReducible (isDefEq preAtomNorm available[i]!.1) then
          available := available.set! i (available[i]!.1, false)
          break
  let frame := available.filter (·.2) |>.map (·.1) |>.toList
  return postAtomsNorm ++ frame

/-- Extract instruction atoms `(addr, instrExpr)` from assertion atoms (legacy). -/
private def extractInstrAtoms (atoms : List Expr) : List (Expr × Expr) :=
  atoms.filterMap fun atom =>
    if atom.isAppOfArity `EvmAsm.instrAt 2 then
      some (atom.getAppArgs[0]!, atom.getAppArgs[1]!)
    else none

/-- Extract instruction entries `(addr, instrExpr)` from a CodeReq expression (pure, no whnf).
    Handles: CodeReq.singleton addr instr, CodeReq.union cr1 cr2 (recursive),
    CodeReq.empty (returns []). -/
private partial def extractCrEntriesPure (cr : Expr) : List (Expr × Expr) :=
  if cr.isAppOfArity ``EvmAsm.CodeReq.singleton 2 then
    let args := cr.getAppArgs
    [(args[0]!, args[1]!)]
  else if cr.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let args := cr.getAppArgs
    extractCrEntriesPure args[0]! ++ extractCrEntriesPure args[1]!
  else []

/-- Extract instruction entries `(addr, instrExpr)` from a CodeReq expression.
    Recursively unfolds abbreviations using whnfR to handle nested CodeReq abbrevs
    (e.g., `evm_gt_code` containing `lt_result_store_code`). -/
private partial def extractCrEntries (cr : Expr) : MetaM (List (Expr × Expr)) := do
  -- Try pure extraction of singleton
  if cr.isAppOfArity ``EvmAsm.CodeReq.singleton 2 then
    let args := cr.getAppArgs
    return [(args[0]!, args[1]!)]
  -- Try union: recursively extract both branches
  if cr.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let args := cr.getAppArgs
    let left ← extractCrEntries args[0]!
    let right ← extractCrEntries args[1]!
    return left ++ right
  -- Not a recognized structural form — try whnfR to unfold one level
  let cr' ← Lean.Meta.whnfR cr
  if cr' == cr then return []  -- No progress, give up
  -- Recurse on the unfolded expression
  extractCrEntries cr'

/-- Auto-resolve all specs from the CodeReq and compose them.
    Extracts instruction entries from cr, resolves each spec using the current state,
    and advances the state between instructions. -/
private def autoResolveAndCompose (goalPre : Expr) (goalCr : Expr) : MetaM Expr := do
  -- Try new-style: extract instructions from CodeReq (cr)
  let mut instrAtoms ← extractCrEntries goalCr
  -- Fallback: if CodeReq is empty/unknown, try legacy instrAt in precondition
  if instrAtoms.isEmpty then
    let atoms ← flattenSepConj goalPre
    instrAtoms := extractInstrAtoms atoms
  if instrAtoms.isEmpty then
    throwError "runBlock: no instructions found in the goal's CodeReq or precondition.\n\
        The goal must be a `cpsTriple` whose CodeReq contains `CodeReq.singleton` entries,\n\
        or whose precondition contains `instrAt` (↦ᵢ) atoms."
  -- All precondition atoms are state atoms (instrAt atoms in legacy mode are also kept)
  let atoms ← flattenSepConj goalPre
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
  trace[runBlock] "all {specs.size} spec(s) resolved, normalizing addresses..."
  -- Normalize addresses in resolved specs (signExtend12, address flattening)
  -- before composition, so postcondition of spec N matches precondition of spec N+1.
  let normalizedSpecs ← specs.mapM fun spec => do
    try normalizeSpecAddresses spec
    catch _ => Pure.pure spec
  trace[runBlock] "composing {normalizedSpecs.size} spec(s)..."
  runBlockCore normalizedSpecs goalPre goalCr

/-- Verify a basic block by composing instruction specs with automatic framing.

    **Auto mode** (no arguments): resolves specs from the `@[spec_gen]` database.
    ```
    runBlock
    ```

    **Manual mode** (with hypotheses): composes the given `cpsTriple` proofs.
    ```
    runBlock s1 s2 s3
    ```

    The goal must be a `cpsTriple entry exit cr pre post`. In auto mode, the
    precondition must contain `instrAt` (`↦ᵢ`) atoms for each instruction.

    **Debugging**: use `set_option trace.runBlock true` to see resolution details. -/
elab "runBlock" specs:ident* : tactic => withMainContext do
  let mvarGoal ← getMainGoal
  -- Strip leading let bindings and metadata from goal type
  let goalType := inlineLets (← instantiateMVars (← mvarGoal.getType))
  let some (_, _, goalCr, _, _) ← parseCpsTriple? goalType
    | throwError "runBlock: goal is not a `cpsTriple`.\n\
        Expected goal of the form: `cpsTriple entry exit cr pre post`."
  -- If the CodeReq is an abbrev application (not CodeReq.singleton/union/empty), delta-unfold it
  -- in the actual goal so all proof terms share the same expression. This prevents deep isDefEq
  -- between abbrev'd and expanded CodeReq (CodeReq = Addr → Option Instr, equality is costly).
  let mvarGoal ← do
    let crEntries := extractCrEntriesPure goalCr
    if crEntries.isEmpty then
      -- goalCr is not structurally a union/singleton — check if it's a named definition to unfold
      match goalCr.getAppFn with
      | .const name _ =>
        -- Skip CodeReq.singleton/union/empty themselves
        if name == ``EvmAsm.CodeReq.singleton || name == ``EvmAsm.CodeReq.union ||
           name == ``EvmAsm.CodeReq.empty then
          Pure.pure mvarGoal
        else
          trace[runBlock] "deltaTarget: unfolding CodeReq abbrev {name}"
          try mvarGoal.deltaTarget (· == name)
          catch e => trace[runBlock] "deltaTarget failed: {e.toMessageData}"; Pure.pure mvarGoal
      | _ => Pure.pure mvarGoal
    else Pure.pure mvarGoal
  -- Re-parse goal after potential delta-unfolding
  let goalType := inlineLets (← instantiateMVars (← mvarGoal.getType))
  let some (_, _, goalCr, goalPre, _) ← parseCpsTriple? goalType
    | throwError "runBlock: goal is not a `cpsTriple` after CodeReq normalization."
  let composed ←
    if specs.isEmpty then
      -- Auto mode: resolve specs from precondition
      autoResolveAndCompose goalPre goalCr
    else
      -- Manual mode: use provided specs
      let specExprs ← specs.mapM fun s => elabTerm s none
      runBlockCore specExprs goalPre goalCr (normalizeAddrs := true)
  let finalResult ← normalizeToGoal composed goalType
  -- Always permute postcondition to match goal (goal.assign doesn't type-check)
  let some (gEntry, gExit, gCr, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "runBlock: internal error — goal lost cpsTriple structure during permutation"
  let resultType ← inferType finalResult
  let some (_, _, _, _, resultPost) ← parseCpsTriple? resultType
    | throwError "runBlock: internal error — composed result is not a cpsTriple"
  -- cpsTriple_consequence (entry exit_ cr P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple entry exit_ cr P Q) : cpsTriple entry exit_ cr P' Q'
  -- P = gPre (what finalResult has), P' = gPre (same, identity), Q = resultPost, Q' = goalPost
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  let permuted := mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[gEntry, gExit, gCr, gPre, gPre, resultPost, goalPost, idPre, postPerm, finalResult]
  mvarGoal.assign permuted
  replaceMainGoal []

end EvmAsm.Tactics
