/-
  EvmAsm.Rv64.Tactics.RunBlock

  Multi-instruction block verification tactic. Composes N single-instruction
  specs into a single cpsTriple proof with automatic framing, address
  normalization, and postcondition permutation.

  ## Quick Reference

  **Auto mode** (preferred — resolves specs from `@[spec_gen_rv64]` database):
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
  2. For each instruction, looks up matching `@[spec_gen_rv64]` specs and
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
  #spec_db  -- prints all @[spec_gen_rv64] entries grouped by instruction
  ```

  ## When Auto Mode Fails

  Common reasons and fixes:
  - **Missing spec**: Check `#spec_db` for coverage. Add `@[spec_gen_rv64]` to your spec.
  - **Proof obligation unsolved**: Auto-mode handles `rd ≠ .x0`, `rd ≠ rs`, and
    `isValidMemAccess` hypotheses. Other obligations need manual specs or extra hyps.
  - **Composite specs**: Multi-instruction sub-specs (e.g., `add_limb_carry_spec`)
    can't be auto-resolved. Use manual mode: `runBlock s1 s2`.
-/

import Lean
import EvmAsm.Rv64.Tactics.SeqFrame
import EvmAsm.Rv64.Tactics.SpecDb

open Lean Meta Elab Tactic

initialize registerTraceClass `runBlock (inherited := true)

namespace EvmAsm.Rv64.Tactics

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
-- Section: Address Normalization for Sub-Spec Composition
-- ============================================================================

/-- Check if an expression is a numeric literal (OfNat.ofNat _ n _) and return n. -/
private def getBvLitVal? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getAppArgs[1]! with
    | .lit (.natVal n) => some n
    | _ => none
  else none

/-- Try to prove `old = new` using fast reflection lemmas (no tactic overhead).
    Handles: `base + 0 = base`, `(base + k1) + k2 = base + sum`, `base + k = base + k`.
    Returns `none` if the pattern doesn't match. -/
private def proveAddrEqFast (old new_ : Expr) : MetaM (Option Expr) := do
  -- Case: old = lhs + rhs
  if old.isAppOfArity ``HAdd.hAdd 6 then
    let oldArgs := old.getAppArgs
    -- Check it's BitVec/Word addition
    unless oldArgs[0]!.isAppOfArity ``BitVec 1 do return none
    let lhs := oldArgs[4]!
    let rhs := oldArgs[5]!
    -- Case: base + 0 = base (new_ is just lhs)
    if let some 0 := getBvLitVal? rhs then
      if lhs == new_ then
        return some (mkApp (mkConst ``EvmAsm.Rv64.addr_add_zero_bv) lhs)
    -- Case: (a + k1) + k2 = a + sum
    if let some rhsVal := getBvLitVal? rhs then
      if lhs.isAppOfArity ``HAdd.hAdd 6 then
        let innerArgs := lhs.getAppArgs
        let a := innerArgs[4]!
        let k1 := innerArgs[5]!
        if let some k1Val := getBvLitVal? k1 then
          -- Check new_ = a + sum
          if new_.isAppOfArity ``HAdd.hAdd 6 then
            let newArgs := new_.getAppArgs
            if newArgs[4]! == a then
              if let some sumVal := getBvLitVal? newArgs[5]! then
                if k1Val + rhsVal == sumVal then
                  try
                    let sumLit := newArgs[5]!
                    let sumEqType ← mkEq (← mkAppM ``HAdd.hAdd #[k1, rhs]) sumLit
                    let hSum ← mkDecideProof sumEqType
                    return some (mkApp5 (mkConst ``EvmAsm.Rv64.addr_reassoc) a k1 rhs sumLit hSum)
                  catch _ => (Pure.pure PUnit.unit : MetaM PUnit)
  return none

/-- Prove `old = new` via fast reflection, then `bv_omega` fallback. Returns `none` on failure. -/
private def proveBvEq (old new_ : Expr) : MetaM (Option Expr) := do
  if ← withoutModifyingState (isDefEq old new_) then
    return some (← mkEqRefl old)
  -- Fast reflection path (avoids tactic overhead)
  if let some pf ← proveAddrEqFast old new_ then return some pf
  let eqType ← mkEq old new_
  -- bv_omega via tactic
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| bv_omega)
    runTacticSilent eqMVar.mvarId! stx
    return some (← instantiateMVars eqMVar)
  catch _ =>
    (Pure.pure PUnit.unit : MetaM PUnit)
  -- Fallback: normalize signExtend12 then bv_omega (handles (sp + K) + signExtend12 N)
  let eqMVar2 ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| simp only [signExtend12_0, signExtend12_8, signExtend12_16, signExtend12_24, signExtend12_32, signExtend12_40, signExtend12_48, signExtend12_56, signExtend12_4095, signExtend12_4088, signExtend12_4080, signExtend12_4072, signExtend12_4064, signExtend12_4056, signExtend12_4048, signExtend12_4040, signExtend12_4032, signExtend12_4024, signExtend12_4016, signExtend12_4008, signExtend12_4000, signExtend12_3992, signExtend12_3984, signExtend12_3976, signExtend12_3968, signExtend12_3960, signExtend12_3952, signExtend12_3944] <;> bv_omega)
    runTacticSilent eqMVar2.mvarId! stx
    return some (← instantiateMVars eqMVar2)
  catch _ => return none

/-- Prove `old = new` for concrete decidable propositions.
    Uses `mkDecideProof` (no tactic overhead). Falls back to `decide` via `runTactic`. -/
private def proveByDecide (old new_ : Expr) : MetaM (Option Expr) := do
  let eqType ← mkEq old new_
  -- Try mkDecideProof (fast path, avoids runTactic overhead)
  try return some (← mkDecideProof eqType)
  catch _ => (Pure.pure PUnit.unit : MetaM PUnit)
  -- Fallback to decide
  let eqMVar ← mkFreshExprMVar eqType
  try
    let stx ← `(tactic| decide)
    runTacticSilent eqMVar.mvarId! stx
    return some (← instantiateMVars eqMVar)
  catch _ => return none

/-- Try to simplify a fully-recursed expression at the top level:
    - `signExtend12 N` (concrete N) → numeric literal
    - `e + 0` → `e`
    - `(a + lit₁) + lit₂` → `a + (lit₁ + lit₂)` -/
private def trySimplifyTop (e : Expr) : MetaM (Expr × Option Expr) := do
  -- signExtend12 on concrete literal: normalize small positive offsets (< 2048).
  -- Large negative offsets (>= 2048) produce huge 64-bit literals that cause
  -- recursion depth issues in mkDecideProof. Leave them as signExtend12.
  if e.isAppOfArity ``EvmAsm.Rv64.signExtend12 1 then
    let arg := e.getAppArgs[0]!
    if let some argVal := getBvLitVal? arg then
      let n12 := argVal % 4096
      if n12 < 2048 then
        let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
        let resultExpr ← mkNumeral bv64 n12
        if let some pf ← proveByDecide e resultExpr then
          return (resultExpr, some pf)
        if let some pf ← proveBvEq e resultExpr then
          return (resultExpr, some pf)
  -- Address arithmetic at BitVec type
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let args := e.getAppArgs
    let lhs := args[4]!
    let rhs := args[5]!
    -- Fast type check: HAdd.hAdd's γ (result type) arg is args[2].
    -- Check for BitVec n / Word / Word directly, avoiding inferType + whnf.
    let γType := args[2]!
    if γType.isAppOfArity ``BitVec 1 ||
       γType == mkApp (mkConst ``BitVec) (mkNatLit 64) ||
       γType == mkApp (mkConst ``BitVec) (mkNatLit 64) then
      -- e + 0 → e (common after signExtend12 0 normalization)
      if let some 0 := getBvLitVal? rhs then
        -- Fast path: use addr_add_zero_bv (avoids bv_omega overhead)
        try
          let pf := mkApp (mkConst ``EvmAsm.Rv64.addr_add_zero_bv) lhs
          return (lhs, some pf)
        catch _ =>
          if let some pf ← proveBvEq e lhs then
            return (lhs, some pf)
      -- (a + lit₁) + lit₂ → a + (lit₁ + lit₂)
      if let some rhsVal := getBvLitVal? rhs then
        if lhs.isAppOfArity ``HAdd.hAdd 6 then
          let lhsArgs := lhs.getAppArgs
          let b := lhsArgs[5]!
          if let some bVal := getBvLitVal? b then
            let a := lhsArgs[4]!
            let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
            let sumLit ← mkNumeral bv64 (bVal + rhsVal)
            let result ← mkAppM ``HAdd.hAdd #[a, sumLit]
            -- Fast path: use addr_reassoc (avoids bv_omega overhead)
            try
              let sumEqType ← mkEq (← mkAppM ``HAdd.hAdd #[b, rhs]) sumLit
              let hSum ← mkDecideProof sumEqType
              let pf := mkApp5 (mkConst ``EvmAsm.Rv64.addr_reassoc) a b rhs sumLit hSum
              return (result, some pf)
            catch _ =>
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
  -- 1. Recurse into .app sub-expressions first (bottom-up)
  let (e', childPf?) ← match e with
    | .app f a => do
      let (f', fPf?) ← normalizeTypeAddrs f
      let (a', aPf?) ← normalizeTypeAddrs a
      if fPf?.isNone && aPf?.isNone then Pure.pure (e, none)
      else
        let new_ := Expr.app f' a'
        -- Build congruence proof; fall back gracefully when AppBuilder fails
        -- (e.g., `congrArg` fails for dependent functions like `ite` with Decidable instances).
        let pf? : Option Expr ← do
          try
            let pf ← match fPf?, aPf? with
              | some fPf, some aPf => mkCongr fPf aPf
              | some fPf, none => mkCongrFun fPf a
              | none, some aPf => mkCongrArg f aPf
              | none, none => unreachable!
            Pure.pure (some pf : Option Expr)
          catch _ =>
            Pure.pure (none : Option Expr)
        match pf? with
        | some pf => Pure.pure (new_, some pf)
        | none => Pure.pure (e, none)  -- skip normalization for this subtree
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

/-- Expand reducible definitions (abbrevs) in a sepConj assertion tree.
    For each leaf that is NOT a sepConj, applies `withReducible whnf` to unfold abbrevs.
    This preserves the structural associativity of the sepConj tree (only expanding leaves),
    so the result is definitionally equal to the input (kernel can verify by unfolding the abbrev).
    Returns the expanded expression (syntactically equal at sepConj structure level). -/
partial def expandAbbrevsInAssertion (e : Expr) : MetaM Expr := do
  match ← parseSepConj? e with
  | some (l, r) =>
    let l' ← expandAbbrevsInAssertion l
    let r' ← expandAbbrevsInAssertion r
    return mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) l' r'
  | none =>
    -- Leaf: apply whnf to unfold abbrevs (e.g., foo_code k base → instrAt base ... ** ...)
    withReducible (whnf e)

/-- Expand reducible definitions (abbrevs) in a CodeReq tree.
    Recursively walks CodeReq.union/singleton/ofProg/empty structure.
    For unrecognized forms (opaque abbreviations), applies `withReducible whnf` to unfold,
    then recurses. This ensures addresses like `(base+K)+4` become visible
    to `normalizeTypeAddrs` for flattening to `base+(K+4)`. -/
private partial def expandAbbrevsInCodeReq (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 then return e
  if e.isAppOfArity ``EvmAsm.Rv64.CodeReq.empty 0 then return e
  if e.isAppOfArity ``EvmAsm.Rv64.CodeReq.ofProg 2 then return e
  if e.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let args := e.getAppArgs
    let l' ← expandAbbrevsInCodeReq args[0]!
    let r' ← expandAbbrevsInCodeReq args[1]!
    return mkApp2 (mkConst ``EvmAsm.Rv64.CodeReq.union) l' r'
  -- Unrecognized form: try whnf to unfold one level, then recurse
  let e' ← withReducible (whnf e)
  if e' == e then return e  -- No progress
  expandAbbrevsInCodeReq e'

/-- Expand reducible definitions (abbrevs) in the CodeReq, Pre, and Post parts of a cpsTriple proof.
    When a spec's type contains `foo_code N (base+K)`, this expands it to its CodeReq chain
    so that `normalizeTypeAddrs` can later simplify addresses like `(base+K)+4 → base+(K+4)`.
    Preserves tree structure (only expands leaf abbrevs, not the chains themselves),
    so the result is definitionally equal to the original — uses Eq.mp with rfl for transport. -/
private def expandAbbrevsInCpsTriple (proof : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType proof)
  let cleanTy := inlineLets ty
  let some (entry, exit_, cr, pre, post) ← parseCpsTriple? cleanTy | return proof
  -- Expand abbrevs in CodeReq, pre, and post
  let crNew ← expandAbbrevsInCodeReq cr
  let preNew ← expandAbbrevsInAssertion pre
  let postNew ← expandAbbrevsInAssertion post
  -- If nothing changed (no abbrevs expanded), return original proof unchanged
  if crNew == cr && preNew == pre && postNew == post then
    return proof
  -- Build new type with expanded parts
  let newTy := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple) #[entry, exit_, crNew, preNew, postNew]
  -- Build proof that ty = newTy via definitional equality (abbrev expansion is definitional).
  -- Use @id (ty = newTy) (Eq.refl ty) to get a term with SYNTACTIC type ty = newTy.
  -- The kernel accepts Eq.refl ty : ty = newTy iff ty =def= newTy.
  -- We pre-check via isDefEq to avoid silent kernel failures.
  if ¬(← withoutModifyingState (isDefEq ty newTy)) then
    return proof  -- fallback: not definitionally equal (shouldn't happen for well-formed abbrevs)
  let eqTy ← mkEq ty newTy
  let eqProof := mkApp2 (mkConst ``id [Level.zero]) eqTy (← mkEqRefl ty)
  mkEqMP eqProof proof

/-- Normalize addresses in a cpsTriple proof.
    First inlines `let` bindings (which are definitionally equal),
    expands reducible abbreviations (abbrevs) in the assertion parts so that
    compound addresses like `(base+N)+M` become `base+(N+M)`,
    then eliminates `signExtend12 N` for concrete N and flattens address arithmetic.
    Transports the original proof via `Eq.mp` (works because cpsTriple is Prop-valued). -/
private def normalizeSpecAddresses (proof : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.normalize (fun _ => return m!"normalizeSpecAddresses") do
  let _origType ← instantiateMVars (← inferType proof)
  -- Inline let-bindings first (e.g., `let mem := sp + signExtend12 off; ...`)
  -- Expand abbrevs in assertions: unfolds `foo_code N (base+K)` so normalizeTypeAddrs
  -- can normalize the resulting `(base+K)+4` addresses.
  let expandedProof ← do
    try expandAbbrevsInCpsTriple proof
    catch _ => Pure.pure proof
  let expandedType ← instantiateMVars (← inferType expandedProof)
  let workType := inlineLets expandedType
  let (_, normPf?) ← normalizeTypeAddrs workType
  match normPf? with
  | some pf => mkEqMP pf expandedProof
  | none =>
    -- If let-inlining changed the type shape, wrap with @id to force the clean type
    -- (let-inlined type is definitionally equal, so the kernel accepts it)
    if workType == expandedType then Pure.pure expandedProof
    else Pure.pure (mkApp2 (mkConst ``id [Level.zero]) workType expandedProof)

/-- Normalize the exit address of a cpsTriple proof to match a target address.
    Uses fast reflection when possible, falls back to `bv_omega`. -/
private def normalizeAddr (accExpr : Expr) (targetExit : Expr) : MetaM Expr := do
  let accType ← inferType accExpr
  let some (entry, exit₁, cr, P, Q) ← parseCpsTriple? accType
    | throwError "runBlock: not a cpsTriple"
  if ← withoutModifyingState (isDefEq exit₁ targetExit) then
    return accExpr
  -- Try fast reflection first (avoids tactic overhead)
  let eqProof ← do
    if let some pf ← proveAddrEqFast exit₁ targetExit then
      Pure.pure pf
    else
      -- Fallback: bv_omega
      let eqType ← mkEq exit₁ targetExit
      let eqMVar ← mkFreshExprMVar eqType
      try
        let stx ← `(tactic| bv_omega)
        runTacticSilent eqMVar.mvarId! stx
      catch _ =>
        throwError "runBlock: cannot prove address equality:\n  {exit₁} = {targetExit}"
      instantiateMVars eqMVar
  let addrType ← inferType exit₁
  withLocalDeclD `x addrType fun x => do
    let body := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple) #[entry, x, cr, P, Q]
    let motive ← mkLambdaFVars #[x] body
    let congrProof ← mkCongrArg motive eqProof
    mkEqMP congrProof accExpr

/-- Frame the first spec against the goal precondition and permute.
    Given s1 : cpsTriple entry exit P1 Q1 and goalPre (the goal's precondition),
    returns : cpsTriple entry exit goalPre (Q1 ** Frame) where Frame = goalPre \ P1. -/
private def frameFirstSpec (s1Expr : Expr) (goalPre : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.frame (fun _ => return m!"frameFirstSpec") do
  let s1Type ← inferType s1Expr
  let some (entry, exit_, cr1, preP1, postQ1) ← parseCpsTriple? s1Type
    | throwError "runBlock: first spec is not a cpsTriple"
  -- Compute frame: goalPre atoms not in P1
  let frameAtoms ← computeFrame goalPre preP1
  if frameAtoms.isEmpty then
    -- No frame needed, just permute precondition
    -- cpsTriple_weaken (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
    -- P = preP1 (from s1), P' = goalPre (what we want), hpre : goalPre → preP1
    let prePermProof ← mkPermLambda goalPre preP1
    let postIdProof ← mkIdLambda postQ1
    return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_weaken)
      #[entry, exit_, cr1, preP1, goalPre, postQ1, postQ1, prePermProof, postIdProof, s1Expr]
  -- Build frame expression
  let frameExpr ← buildSepConjChain frameAtoms
  -- Prove pcFree for the frame (direct proof construction, no tactic overhead)
  let pcFreeProof ← try buildPcFreeProof frameExpr
    catch _ => throwError "runBlock: could not prove pcFree for initial frame:\n  {frameExpr}"
  -- Frame s1: cpsTriple entry exit cr1 (P1 ** F) (Q1 ** F)
  let s1Framed := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_frameR)
    #[entry, exit_, cr1, preP1, postQ1, frameExpr, pcFreeProof, s1Expr]
  -- Permute precondition: goalPre → (P1 ** F)
  let p1StarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) preP1 frameExpr
  -- cpsTriple_weaken (P P' Q Q') (hpre : P' → P) (hpost : Q → Q') (h : cpsTriple P Q) : cpsTriple P' Q'
  -- P = p1StarFrame (from s1Framed), P' = goalPre, hpre : goalPre → p1StarFrame
  let prePermProof ← mkPermLambda goalPre p1StarFrame
  let q1StarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) postQ1 frameExpr
  let postIdProof ← mkIdLambda q1StarFrame
  return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_weaken)
    #[entry, exit_, cr1, p1StarFrame, goalPre, q1StarFrame, q1StarFrame,
      prePermProof, postIdProof, s1Framed]

/-- Core: compose an array of cpsTriple proofs with initial framing,
    address normalization, and seqFrame chaining.
    When `goalCr` is provided, extends each spec's CodeReq to goalCr before composition
    so that all specs share the same CR (enabling the same-CR fast path in seqFrame).
    Always normalizes spec addresses (signExtend12 reduction and address arithmetic flattening)
    so that atoms match the normalized goal. -/
private def runBlockCore (specs : Array Expr) (goalPre : Expr)
    (goalCr : Option Expr := none) : MetaM Expr :=
  withTraceNode `runBlock.perf (fun _ => return m!"runBlockCore ({specs.size} specs)") do
  if specs.size == 0 then
    throwError "runBlock: no specs provided.\n\
        Usage: `runBlock s1 s2 ...` (manual) or `runBlock` (auto from @[spec_gen_rv64] database)."
  -- Always normalize addresses in specs (signExtend12, address flattening)
  let processedSpecs ← withTraceNode `runBlock.perf.normalize
    (fun _ => return m!"normalize {specs.size} specs") do
    specs.mapM fun spec => do
      try normalizeSpecAddresses spec
      catch _ => Pure.pure spec
  -- Extend specs to goalCr if provided
  let extendedSpecs ← withTraceNode `runBlock.perf.extend
    (fun _ => return m!"extend {processedSpecs.size} specs to goalCr") do
    match goalCr with
    | some gcr => do
        -- Pre-extract the goal CR chain once (O(N)) for direct proof building
        let goalChain ← extractUnionChain gcr
        processedSpecs.mapM fun spec => do
          let specType ← inferType spec
          let some (entry, exit_, specCr, P, Q) ← parseCpsTriple? specType | Pure.pure spec
          if specCr == gcr then Pure.pure spec
          else if ← withoutModifyingState (withReducible (isDefEq specCr gcr)) then Pure.pure spec
          else try
            -- Fast path: direct chain lookup for singleton specs (O(position) per spec)
            if let some monoProof ← buildMonoProofDirect specCr goalChain gcr then
              Pure.pure (mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_extend_code)
                #[entry, exit_, specCr, gcr, P, Q, monoProof, spec])
            else
              extendSpecCr spec specCr gcr
          catch _ => Pure.pure spec
    | none => Pure.pure processedSpecs
  -- Frame the first spec against the goal precondition
  let mut acc ← frameFirstSpec extendedSpecs[0]! goalPre
  -- Chain remaining specs via seqFrame with address normalization
  for i in [1:extendedSpecs.size] do
    acc ← withTraceNode `runBlock.perf.seq
      (fun _ => return m!"seqFrame step {i}/{extendedSpecs.size - 1}") do
        let nextSpec := extendedSpecs[i]!
        let nextType ← inferType nextSpec
        let some (nextEntry, _, _, _, _) ← parseCpsTriple? nextType
          | throwError "runBlock: argument {i + 1} is not a cpsTriple"
        let acc' ← normalizeAddr acc nextEntry
        seqFrameCore acc' nextSpec
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

/-- Extract the target address from `isValidDwordAccess target = true`. -/
private def parseIsValidDwordAccess? (ty : Expr) : MetaM (Option Expr) := do
  if !ty.isAppOfArity ``Eq 3 then return none
  let args := ty.getAppArgs
  let lhs := args[1]!
  let rhs := args[2]!
  unless rhs == mkConst ``Bool.true do return none
  if lhs.isAppOfArity ``EvmAsm.Rv64.isValidDwordAccess 1 then
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
    Handles: `validAddr` (offset 0), `validAddr + lit`, `validAddr + signExtend12 lit`,
    `(validAddr + lit₁) + lit₂` (nested additions). -/
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
      -- rhs is signExtend12 N (64-bit: 12-bit sign-extend to 64-bit)
      if rhs.isAppOfArity ``EvmAsm.Rv64.signExtend12 1 then
        let arg := rhs.getAppArgs[0]!
        if let some argVal := getBvLitVal? arg then
          let n12 := argVal % 4096
          return some (if n12 < 2048 then n12 else n12 + (2^64 - 4096))
    -- Case 3: target = (validAddr + lit₁) + lit₂  (nested addition)
    -- Also handles (validAddr + lit₁) + signExtend12 lit₂
    if lhs.isAppOfArity ``HAdd.hAdd 6 then
      let innerLhs := lhs.getAppArgs[4]!
      let innerRhs := lhs.getAppArgs[5]!
      if ← withoutModifyingState (isDefEq validAddr innerLhs) then
        if let some v1 := getBvLitVal? innerRhs then
          -- (validAddr + v1) + rhs
          if let some v2 := getBvLitVal? rhs then return some (v1 + v2)
          if rhs.isAppOfArity ``EvmAsm.Rv64.signExtend12 1 then
            let arg := rhs.getAppArgs[0]!
            if let some argVal := getBvLitVal? arg then
              let n12 := argVal % 4096
              let v2 := if n12 < 2048 then n12 else n12 + (2^64 - 4096)
              return some (v1 + v2)
    -- Case 4: target = X + B, validAddr = X + A  (offset = B - A mod 2^64)
    -- Handles different concrete offsets from the same base register.
    -- B can be a numeric literal or signExtend12 N.
    if validAddr.isAppOfArity ``HAdd.hAdd 6 then
      let addrBase := validAddr.getAppArgs[4]!
      let addrOff := validAddr.getAppArgs[5]!
      if ← withoutModifyingState (isDefEq addrBase lhs) then
        if let some a := getBvLitVal? addrOff then
          -- B is a numeric literal
          if let some b := getBvLitVal? rhs then
            return some ((b + 2^64 - a) % (2^64))
          -- B is signExtend12 N
          if rhs.isAppOfArity ``EvmAsm.Rv64.signExtend12 1 then
            let arg := rhs.getAppArgs[0]!
            if let some argVal := getBvLitVal? arg then
              let n12 := argVal % 4096
              let b := if n12 < 2048 then n12 else n12 + (2^64 - 4096)
              return some ((b + 2^64 - a) % (2^64))
  return none

/-- Build a proof of `ValidMemRange.fetch` for a given index (64-bit, stride 8). -/
private def buildFetchProof (validAddr validN : Expr) (validHyp : Expr)
    (i : Nat) (nVal : Nat) (target : Expr) : MetaM (Option Expr) := do
  if i >= nVal then return none
  let eightI := mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit (8 * i))
  let indexedAddr ← mkAppM ``HAdd.hAdd #[validAddr, eightI]
  let some eqProof ← proveBvEq indexedAddr target | return none
  let iLtN ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit i, validN])
  return some (mkAppN (mkConst ``EvmAsm.Rv64.ValidMemRange.fetch)
    #[validAddr, validN, validHyp, mkNatLit i, target, iLtN, eqProof])

/-- Try to prove `isValidDwordAccess target = true` from ValidMemRange hypotheses.
    Searches for `ValidMemRange addr n` hypotheses and uses `ValidMemRange.fetch`. -/
private def solveFromValidMemRange (ty : Expr) : MetaM (Option Expr) := do
  let some target ← parseIsValidDwordAccess? ty | return none
  let lctx ← getLCtx
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if !declType.isAppOfArity ``EvmAsm.Rv64.ValidMemRange 2 then continue
    let validAddr := declType.getAppArgs[0]!
    let validN := declType.getAppArgs[1]!
    let some nVal := getNatLitVal? validN | continue
    -- Fast path: extract concrete offset and compute index directly
    if let some offset ← extractConcreteOffset? validAddr target then
      if offset % 8 == 0 then
        let i := offset / 8
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
private def solveObligation (mvarId : MVarId) : MetaM Bool :=
  withTraceNode `runBlock.perf.obligation (fun _ => return m!"solveObligation") do
  let ty ← instantiateMVars (← mvarId.getType)
  -- Try Decidable proof for concrete propositions (rd ≠ .x0, rd ≠ rs, etc.)
  if ← isConcreteDecidable ty then
    try
      let proof ← mkDecideProof ty
      mvarId.assign proof
      return true
    catch _ =>
      (Pure.pure PUnit.unit : MetaM PUnit)
  -- Try searching local context (handles isValidDwordAccess from hypotheses)
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
    runTacticSilent mvarId stx
    return true
  catch _ =>
    return false

/-- Tactic to derive `isValidDwordAccess target = true` from `ValidMemRange` in context.
    Searches for `ValidMemRange addr n` hypotheses and uses `ValidMemRange.fetch`.
    Normalizes `signExtend12` in the goal first to handle compound address forms. -/
elab "validMem" : tactic => do
  -- First normalize signExtend12 in the goal (handles (sp + K) + signExtend12 N patterns)
  try
    evalTactic (← `(tactic| simp only [signExtend12_0, signExtend12_1, signExtend12_8,
      signExtend12_16, signExtend12_24, signExtend12_32, signExtend12_40,
      signExtend12_48, signExtend12_56,
      signExtend12_4095, signExtend12_4088, signExtend12_4080,
      signExtend12_4072, signExtend12_4064, signExtend12_4056,
      signExtend12_4048, signExtend12_4040, signExtend12_4032,
      signExtend12_4024, signExtend12_4016, signExtend12_4008,
      signExtend12_4000, signExtend12_3992, signExtend12_3984,
      signExtend12_3976, signExtend12_3968, signExtend12_3960,
      signExtend12_3952, signExtend12_3944]))
  catch _ =>
    (Pure.pure PUnit.unit : TacticM PUnit)
  withMainContext do
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
        Expected goal of the form: `isValidDwordAccess target = true`"

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
  -- body should be cpsTriple entry exit cr pre post
  let some (specEntry, _, specCr, specPre, _) ← parseCpsTriple? body
    | throwError "tryInstantiateSpec: {specName} is not a cpsTriple"
  -- Step 1: Unify spec address with our instruction address
  unless ← isDefEq specEntry instrAddr do
    throwError "address mismatch"
  -- Step 1b: Match instruction in specCr (CodeReq.singleton)
  let specCrWhnf ← whnfR specCr
  if specCrWhnf.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 then
    let specInstr := specCrWhnf.getAppArgs[1]!
    unless ← isDefEq specInstr instrExpr do
      throwError "instruction mismatch in cr"
  -- Step 2: Flatten spec precondition and match atoms
  let specAtoms ← flattenSepConj specPre
  -- Step 2a (legacy fallback): Unify instrAt atoms if still present in pre
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.Rv64.instrAt 2 then
      let specInstr := atom.getAppArgs[1]!
      unless ← isDefEq specInstr instrExpr do
        throwError "instruction mismatch"
  -- Step 2b: Unify regIs atoms
  let stateRegAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.Rv64.regIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.Rv64.regIs 2 then
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
  let stateMemAtoms := stateAtoms.filter (·.isAppOfArity `EvmAsm.Rv64.memIs 2)
  for atom in specAtoms do
    if atom.isAppOfArity `EvmAsm.Rv64.memIs 2 then
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
    throwError "runBlock: no @[spec_gen_rv64] specs registered for `{instrName}`.\n\
        Hint: Add `@[spec_gen_rv64]` to a theorem with `{instrName}` in its precondition,\n\
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
    if atom.isAppOfArity `EvmAsm.Rv64.instrAt 2 then
      some (atom.getAppArgs[0]!, atom.getAppArgs[1]!)
    else none

/-- Extract instruction entries `(addr, instrExpr)` from a CodeReq expression (pure, no whnf).
    Handles: CodeReq.singleton addr instr, CodeReq.union cr1 cr2 (recursive),
    CodeReq.empty (returns []). -/
private partial def extractCrEntriesPure (cr : Expr) : List (Expr × Expr) :=
  if cr.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 then
    let args := cr.getAppArgs
    [(args[0]!, args[1]!)]
  else if cr.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let args := cr.getAppArgs
    extractCrEntriesPure args[0]! ++ extractCrEntriesPure args[1]!
  else []

/-- Walk a concrete `List Instr` (whnf'd) and emit `(base + 4*k, instr)` entries. -/
private partial def extractProgEntries (base : Expr) (progList : Expr) (off : Nat := 0) :
    MetaM (List (Expr × Expr)) := do
  let listW ← whnf progList
  if listW.isAppOfArity ``List.cons 3 then
    let headInstr := listW.getAppArgs[1]!
    let rest := listW.getAppArgs[2]!
    let addrType := mkApp (mkConst ``BitVec) (mkNatLit 64)
    let addr ← if off == 0 then Pure.pure base
      else do let offBv ← Lean.Meta.mkNumeral addrType off; mkAppM ``HAdd.hAdd #[base, offBv]
    let tail ← extractProgEntries base rest (off + 4)
    return (addr, headInstr) :: tail
  else
    return []

/-- Extract instruction entries `(addr, instrExpr)` from a CodeReq expression.
    Recursively unfolds abbreviations using whnfR to handle nested CodeReq abbrevs.
    Also handles CodeReq.ofProg by enumerating (base + 4*k, prog[k]) entries. -/
private partial def extractCrEntries (cr : Expr) : MetaM (List (Expr × Expr)) := do
  if cr.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 then
    let args := cr.getAppArgs
    return [(args[0]!, args[1]!)]
  if cr.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let args := cr.getAppArgs
    let left ← extractCrEntries args[0]!
    let right ← extractCrEntries args[1]!
    return left ++ right
  -- Case: ofProg base prog — enumerate entries from the program list
  if cr.isAppOfArity ``EvmAsm.Rv64.CodeReq.ofProg 2 then
    let base := cr.getAppArgs[0]!
    let prog := cr.getAppArgs[1]!
    return ← extractProgEntries base prog
  -- Not a recognized structural form — try whnfR to unfold one level
  let cr' ← Lean.Meta.whnfR cr
  if cr' == cr then return []  -- No progress, give up
  extractCrEntries cr'

/-- Auto-resolve all specs from the CodeReq/precondition and compose them.
    Tries CodeReq first (new-style: instructions in `cr`), falls back to
    instrAt atoms in precondition (legacy). -/
private def autoResolveAndCompose (goalPre : Expr) (goalCr : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf (fun _ => return m!"autoResolveAndCompose") do
  -- Try new-style: extract instructions from CodeReq
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
  let stateAtoms := atoms.filter fun a => !a.isAppOfArity `EvmAsm.Rv64.instrAt 2
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
  runBlockCore specs goalPre (goalCr := some goalCr)

/-- Verify a basic block by composing instruction specs with automatic framing.

    **Auto mode** (no arguments): resolves specs from the `@[spec_gen_rv64]` database.
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
  withTraceNode `runBlock.perf (fun _ => return m!"runBlock") do
    let mvarGoal ← getMainGoal
    -- Strip leading let bindings and metadata from goal type
    let goalType := inlineLets (← instantiateMVars (← mvarGoal.getType))
    let some (_, _, goalCr, _, _) ← parseCpsTriple? goalType
      | throwError "runBlock: goal is not a `cpsTriple`.\n\
          Expected goal of the form: `cpsTriple entry exit cr pre post`."
    -- If the CodeReq is an abbrev application (not CodeReq.singleton/union/empty), delta-unfold it
    -- in the actual goal so all proof terms share the same expression.
    let mvarGoal ← do
      let crEntries := extractCrEntriesPure goalCr
      if crEntries.isEmpty then
        match goalCr.getAppFn with
        | .const name _ =>
          if name == ``EvmAsm.Rv64.CodeReq.singleton || name == ``EvmAsm.Rv64.CodeReq.union ||
             name == ``EvmAsm.Rv64.CodeReq.empty then
            Pure.pure mvarGoal
          else
            trace[runBlock] "deltaTarget: unfolding CodeReq abbrev {name}"
            try mvarGoal.deltaTarget (· == name)
            catch _ => Pure.pure mvarGoal
        | _ => Pure.pure mvarGoal
      else Pure.pure mvarGoal
    -- Re-parse goal after potential delta-unfolding
    let goalType := inlineLets (← instantiateMVars (← mvarGoal.getType))
    -- Normalize addresses in goal type (signExtend12, e+0, address flattening)
    let (normGoalType, goalNormPf?) ← normalizeTypeAddrs goalType
    let (workingGoal, workingGoalType) ← if let some pf := goalNormPf? then do
        let newGoalMVar ← mkFreshExprMVar normGoalType
        let proof ← mkEqMP (← mkEqSymm pf) newGoalMVar
        mvarGoal.assign proof
        Pure.pure (newGoalMVar.mvarId!, normGoalType)
      else Pure.pure (mvarGoal, goalType)
    let some (_, _, goalCr, goalPre, _) ← parseCpsTriple? workingGoalType
      | throwError "runBlock: goal is not a `cpsTriple` after normalization."
    let composed ←
      if specs.isEmpty then
        -- Auto mode: resolve specs from CodeReq/precondition
        autoResolveAndCompose goalPre goalCr
      else
        -- Manual mode: use provided specs
        let specExprs ← specs.mapM fun s => elabTerm s none
        runBlockCore specExprs goalPre (goalCr := some goalCr)
    let finalResult ← normalizeToGoal composed workingGoalType
    -- Always permute postcondition to match goal
    let some (gEntry, gExit, gCr, gPre, goalPost) ← parseCpsTriple? workingGoalType
      | throwError "runBlock: internal error — goal lost cpsTriple structure during permutation"
    let resultType ← inferType finalResult
    let some (_, _, _, _, resultPost) ← parseCpsTriple? resultType
      | throwError "runBlock: internal error — composed result is not a cpsTriple"
    let postPerm ← mkPermLambda resultPost goalPost
    let idPre ← mkIdLambda gPre
    let permuted := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_weaken)
      #[gEntry, gExit, gCr, gPre, gPre, resultPost, goalPost, idPre, postPerm, finalResult]
    workingGoal.assign permuted
    replaceMainGoal []

end EvmAsm.Rv64.Tactics
