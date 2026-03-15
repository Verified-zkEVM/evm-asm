/-
  EvmAsm.Rv32.Tactics.SeqFrame

  Frame-aware sequential composition of two `cpsTriple` specs.

  ## Usage

  ```
  have s1 : cpsTriple base mid P Q1 := ...
  have s2 : cpsTriple mid exit_ P2 Q2 := ...
  seqFrame s1 s2
  -- Result: cpsTriple base exit_ P (Q2 ** Frame)
  -- where Frame = Q1 \ P2 (postcondition atoms not consumed by s2's precondition)
  ```

  ## Algorithm

  1. Extracts postcondition Q1 of h1 and precondition P2 of h2
  2. Computes frame F = Q1 \ P2 (atoms in Q1 not matched by P2)
  3. Frames h2: `cpsTriple_frame_left` produces `cpsTriple mid exit (P2 ** F) (Q2 ** F)`
  4. Builds permutation proof Q1 → (P2 ** F)
  5. Composes via `cpsTriple_seq_with_perm`

  If the goal is a `cpsTriple`, `seqFrame` tries to close it (with postcondition
  permutation). Otherwise, the result is introduced as a hypothesis named `h1h2`.
-/

import Lean
import EvmAsm.Rv32.Tactics.XCancel
import EvmAsm.Rv32.SyscallSpecs

open Lean Meta Elab Tactic

namespace EvmAsm.Tactics

/-- Parse `cpsTriple entry exit_ cr P Q` returning the five arguments.
    Does NOT whnf (which would unfold the def). -/
def parseCpsTriple? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``EvmAsm.cpsTriple 5 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  return none

/-- Given Q1 (postcondition of h1) and P2 (precondition of h2),
    find atoms of P2 within Q1 and return the frame (residual Q1 atoms).
    Both sides are first reassociated to right-associated form for proper flattening.
    Uses hash pre-filtering to reduce expensive `isDefEq` calls. -/
def computeFrame (q1 p2 : Expr) : MetaM (List Expr) := do
  -- Reassociate to right-associated form before flattening
  let (q1RA, _) ← reassocProof q1
  let (p2RA, _) ← reassocProof p2
  let q1Atoms := (← flattenSepConj q1RA).toArray
  let p2Atoms := (← flattenSepConj p2RA).toArray
  let mut available := (Array.mk (List.replicate q1Atoms.size true) : Array Bool)
  for p2Atom in p2Atoms do
    let h := p2Atom.hash
    let mut found := false
    -- Fast path: check atoms with matching hash first
    for i in [:q1Atoms.size] do
      if available[i]! && q1Atoms[i]!.hash == h then
        if ← withReducible (isDefEq p2Atom q1Atoms[i]!) then
          available := available.set! i false
          found := true
          break
    -- Slow path: remaining atoms (handles hash mismatch + definitional equality)
    unless found do
      for i in [:q1Atoms.size] do
        if available[i]! && q1Atoms[i]!.hash != h then
          if ← withReducible (isDefEq p2Atom q1Atoms[i]!) then
            available := available.set! i false
            found := true
            break
    unless found do
      throwError "seqFrame: h2's precondition atom not found in h1's postcondition:\n  {p2Atom}\n\
          Hint: h1's postcondition must contain all atoms needed by h2's precondition."
  let mut result : List Expr := []
  for i in [:q1Atoms.size] do
    if available[i]! then
      result := result ++ [q1Atoms[i]!]
  return result

/-- Build a `pcFree` proof directly in MetaM, avoiding tactic overhead.
    Handles all standard assertion types; falls back to the `pcFree` tactic for unknowns. -/
partial def buildPcFreeProof (assertion : Expr) : MetaM Expr := do
  let e ← normForSepConj assertion
  if e.isAppOfArity ``EvmAsm.sepConj 2 then
    let l := Expr.appArg! (Expr.appFn! e)
    let r := Expr.appArg! e
    let lPf ← buildPcFreeProof l
    let rPf ← buildPcFreeProof r
    return mkApp4 (mkConst ``EvmAsm.pcFree_sepConj) l r lPf rPf
  else if e.isAppOfArity `EvmAsm.instrAt 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.pcFree_instrAt) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.regIs 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.pcFree_regIs) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.memIs 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.pcFree_memIs) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.regOwn 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_regOwn) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.memOwn 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_memOwn) e.getAppArgs[0]!
  else if e == mkConst ``EvmAsm.empAssertion then
    return mkConst ``EvmAsm.pcFree_emp
  else if e.isAppOfArity `EvmAsm.pure 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_pure) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.publicValuesIs 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_publicValuesIs) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.privateInputIs 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_privateInputIs) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.programAt 1 then
    return mkApp (mkConst ``EvmAsm.pcFree_programAt) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.progAt 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.pcFree_progAt) args[0]! args[1]!
  else
    -- Fallback to tactic for unknown assertion types
    let pcFreeType := mkApp (mkConst ``EvmAsm.Assertion.pcFree) assertion
    let pcFreeMVar ← mkFreshExprMVar pcFreeType
    let stx ← `(tactic| pcFree)
    let _ ← Lean.Elab.runTactic pcFreeMVar.mvarId! stx
    instantiateMVars pcFreeMVar

/-- Build a lambda `fun (h : PartialState) (hp : P h) => proof h hp`
    where proof converts `P h` to `Q h` using a permutation equality `P = Q`. -/
def mkPermLambda (src tgt : Expr) : MetaM Expr := do
  let permProof ← buildPermProof src tgt
  let psType := mkConst ``EvmAsm.PartialState
  withLocalDeclD `h psType fun h => do
    withLocalDeclD `hp (mkApp src h) fun hp => do
      let proof ← mkEqMP (← mkCongrFun permProof h) hp
      mkLambdaFVars #[h, hp] proof

/-- Build identity lambda: `fun (h : PartialState) (hp : P h) => hp` -/
def mkIdLambda (p : Expr) : MetaM Expr := do
  let psType := mkConst ``EvmAsm.PartialState
  withLocalDeclD `h psType fun h =>
    withLocalDeclD `hp (mkApp p h) fun hp =>
      mkLambdaFVars #[h, hp] hp

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

/-- Build a proof of `CodeReq.Disjoint cr1 cr2` by structural recursion.
    Handles: empty, singleton vs singleton (bv_omega for addr ≠),
    union vs anything (recursive). -/
partial def buildDisjointProof (cr1 cr2 : Expr) : MetaM Expr := do
  let cr1 ← whnfR cr1
  let cr2 ← whnfR cr2
  -- empty vs anything
  if cr1 == mkConst ``EvmAsm.CodeReq.empty then
    return ← mkAppM ``EvmAsm.CodeReq.Disjoint.empty_left #[cr2]
  if cr2 == mkConst ``EvmAsm.CodeReq.empty then
    return ← mkAppM ``EvmAsm.CodeReq.Disjoint.empty_right #[cr1]
  -- singleton vs singleton
  if cr1.isAppOfArity ``EvmAsm.CodeReq.singleton 2 &&
     cr2.isAppOfArity ``EvmAsm.CodeReq.singleton 2 then
    let a1 := cr1.getAppArgs[0]!
    let i1 := cr1.getAppArgs[1]!
    let a2 := cr2.getAppArgs[0]!
    let i2 := cr2.getAppArgs[1]!
    let addrType := mkApp (mkConst ``BitVec) (mkNatLit 32)
    let neqType := mkApp3 (mkConst ``Ne [levelOne]) addrType a1 a2
    let neqMVar ← mkFreshExprMVar neqType
    let stx ← `(tactic| bv_omega)
    let _ ← Lean.Elab.runTactic neqMVar.mvarId! stx
    let neqProof ← instantiateMVars neqMVar
    return ← mkAppM ``EvmAsm.CodeReq.Disjoint.singleton #[neqProof, i1, i2]
  -- union on left
  if cr1.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let sub1 := cr1.getAppArgs[0]!
    let sub2 := cr1.getAppArgs[1]!
    let hd1 ← buildDisjointProof sub1 cr2
    let hd2 ← buildDisjointProof sub2 cr2
    return ← mkAppM ``EvmAsm.CodeReq.Disjoint.union_left #[hd1, hd2]
  -- union on right
  if cr2.isAppOfArity ``EvmAsm.CodeReq.union 2 then
    let sub1 := cr2.getAppArgs[0]!
    let sub2 := cr2.getAppArgs[1]!
    let hd1 ← buildDisjointProof cr1 sub1
    let hd2 ← buildDisjointProof cr1 sub2
    return ← mkAppM ``EvmAsm.CodeReq.Disjoint.union_right #[hd1, hd2]
  -- fallback
  throwError "buildDisjointProof: cannot prove CodeReq.Disjoint for:\n  cr1 = {cr1}\n  cr2 = {cr2}"

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
  try
    let stx ← `(tactic| intro a i h; simp only [EvmAsm.CodeReq.singleton, EvmAsm.CodeReq.union] at *; split <;> try simp_all)
    let _ ← Lean.Elab.runTactic mvar.mvarId! stx
    return ← instantiateMVars mvar
  catch _ =>
    try return ← mkDecideProof propType
    catch _ => throwError "seqFrame: cannot build monotonicity proof for CodeReq extension"

/-- Build a proof of `∀ a i, oldCr a = some i → newCr a = some i` structurally.
    Walks the union chain to find matching pieces, composing with
    CodeReq.union_mono_left, mono_union_right, and union_split_mono.
    Falls back to tactic-based proof for edge cases. -/
private partial def buildMonoProof (oldCr newCr : Expr) : MetaM Expr := do
  -- Identity: oldCr ≡ newCr (structural check first to avoid deep isDefEq on CodeReq functions)
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

/-- Core MetaM implementation of seqFrame.
    Returns the composed proof term. -/
def seqFrameCore (h1Expr h2Expr : Expr) : MetaM Expr := do
  let h1Type ← inferType h1Expr
  let h2Type ← inferType h2Expr

  let some (entry, mid1, cr1, preP, postQ1) ← parseCpsTriple? h1Type
    | throwError "seqFrame: first argument is not a cpsTriple"
  let some (mid2, exit_, cr2, preP2, postQ2) ← parseCpsTriple? h2Type
    | throwError "seqFrame: second argument is not a cpsTriple"

  unless ← isDefEq mid1 mid2 do
    throwError "seqFrame: midpoints don't match:\n  h1 exit: {mid1}\n  h2 entry: {mid2}"

  -- Determine effective CR and extended specs
  let (effectiveCr, h1Eff, h2Eff) ←
    if ← withoutModifyingState (isDefEq cr1 cr2) then
      -- Same-CR fast path: skip union/extension
      Pure.pure (cr1, h1Expr, h2Expr)
    else
      -- Different CRs: extend both to combined CR
      let combinedCr ← mkAppM ``EvmAsm.CodeReq.union #[cr1, cr2]
      let h1Extended ← extendSpecCr h1Expr cr1 combinedCr
      let h2Extended ← extendSpecCr h2Expr cr2 combinedCr
      Pure.pure (combinedCr, h1Extended, h2Extended)

  -- Find frame: Q1 atoms not matched by P2
  let frameAtoms ← computeFrame postQ1 preP2

  if frameAtoms.isEmpty then
    -- No frame: compose directly with permutation (avoids spurious empAssertion atom)
    let hperm ← mkPermLambda postQ1 preP2
    return mkAppN (mkConst ``EvmAsm.cpsTriple_seq_with_perm)
      #[entry, mid1, exit_, effectiveCr, preP, postQ1, preP2, postQ2,
        hperm, h1Eff, h2Eff]

  let frameExpr ← buildSepConjChain frameAtoms

  -- Solve pcFree for the frame (direct proof construction, no tactic overhead)
  let pcFreeProof ← try buildPcFreeProof frameExpr
    catch _ => throwError "seqFrame: could not prove pcFree for frame:\n  {frameExpr}"

  -- h2Framed : cpsTriple mid exit_ effectiveCr (P2 ** F) (Q2 ** F)
  let h2Framed := mkAppN (mkConst ``EvmAsm.cpsTriple_frame_left)
    #[mid2, exit_, effectiveCr, preP2, postQ2, frameExpr, pcFreeProof, h2Eff]

  -- Permutation proof: Q1 → (P2 ** F)
  let p2StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) preP2 frameExpr
  let hperm ← mkPermLambda postQ1 p2StarFrame

  -- Compose: cpsTriple_seq_with_perm entry mid exit_ effectiveCr P Q1 (P2**F) (Q2**F) hperm h1 h2Framed
  let q2StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) postQ2 frameExpr
  return mkAppN (mkConst ``EvmAsm.cpsTriple_seq_with_perm)
    #[entry, mid1, exit_, effectiveCr, preP, postQ1, p2StarFrame, q2StarFrame,
      hperm, h1Eff, h2Framed]

/-- Try to assign `result` directly to `goal`, or with a postcondition permutation. -/
def assignOrPermute (goal : MVarId) (result : Expr) : MetaM Unit := do
  let goalType ← goal.getType
  let resultType ← inferType result
  -- Attempt 1: types already match (check without side effects first)
  if ← withoutModifyingState (isDefEq goalType resultType) then
    goal.assign result
    return
  -- Attempt 2: permute postcondition via cpsTriple_consequence
  let some (gEntry, gExit, gCr, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "seqFrame: goal is not a cpsTriple"
  let some (rEntry, rExit, _, _, resultPost) ← parseCpsTriple? resultType
    | throwError "seqFrame: result is not a cpsTriple (internal error)"
  unless ← isDefEq gEntry rEntry do
    throwError "seqFrame: entry addresses don't match goal"
  unless ← isDefEq gExit rExit do
    throwError "seqFrame: exit addresses don't match goal"
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  let finalResult := mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[gEntry, gExit, gCr, gPre, gPre, resultPost, goalPost, idPre, postPerm, result]
  goal.assign finalResult

/-- `seqFrame h1 h2` composes two `cpsTriple` hypotheses with automatic framing.

    Given:
      h1 : cpsTriple entry mid P Q1
      h2 : cpsTriple mid exit_ P2 Q2

    Produces: cpsTriple entry exit_ P (Q2 ** F)
    where F is the frame (Q1 atoms not consumed by P2).

    If the goal is a cpsTriple, the tactic tries to close it directly
    (with postcondition permutation if needed). Otherwise, the result
    is introduced as a named hypothesis `h1h2` (concatenation of the two names). -/
elab "seqFrame" h1:ident h2:ident : tactic => withMainContext do
  let h1Expr ← elabTerm h1 none
  let h2Expr ← elabTerm h2 none
  let result ← seqFrameCore h1Expr h2Expr
  let goal ← getMainGoal
  -- Try to close the goal
  try
    assignOrPermute goal result
    replaceMainGoal []
  catch _ =>
    -- Introduce as a named hypothesis
    let name := Name.mkSimple s!"{h1.getId}{h2.getId}"
    let fvarId ← liftMetaTacticAux (α := FVarId) fun mvarId => do
      let (fvarId, mvarId) ← mvarId.note name result
      return (fvarId, [mvarId])
    -- Register name in elaboration context so subsequent tactics can find it
    withMainContext do
      Term.addLocalVarInfo (mkIdent name) (.fvar fvarId)

end EvmAsm.Tactics
