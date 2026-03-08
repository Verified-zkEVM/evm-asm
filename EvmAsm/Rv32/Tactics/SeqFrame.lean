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

/-- Parse `cpsTriple entry exit_ P Q` returning the four arguments.
    Does NOT whnf (which would unfold the def). -/
def parseCpsTriple? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``EvmAsm.cpsTriple 4 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!)
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

/-- Core MetaM implementation of seqFrame.
    Returns the composed proof term. -/
def seqFrameCore (h1Expr h2Expr : Expr) : MetaM Expr := do
  let h1Type ← inferType h1Expr
  let h2Type ← inferType h2Expr

  let some (entry, mid1, preP, postQ1) ← parseCpsTriple? h1Type
    | throwError "seqFrame: first argument is not a cpsTriple"
  let some (mid2, exit_, preP2, postQ2) ← parseCpsTriple? h2Type
    | throwError "seqFrame: second argument is not a cpsTriple"

  unless ← isDefEq mid1 mid2 do
    throwError "seqFrame: midpoints don't match:\n  h1 exit: {mid1}\n  h2 entry: {mid2}"

  -- Find frame: Q1 atoms not matched by P2
  let frameAtoms ← computeFrame postQ1 preP2
  let frameExpr ← buildSepConjChain frameAtoms

  -- Solve pcFree for the frame (direct proof construction, no tactic overhead)
  let pcFreeProof ← try buildPcFreeProof frameExpr
    catch _ => throwError "seqFrame: could not prove pcFree for frame:\n  {frameExpr}"

  -- h2Framed : cpsTriple mid exit_ (P2 ** F) (Q2 ** F)
  let h2Framed := mkAppN (mkConst ``EvmAsm.cpsTriple_frame_left)
    #[mid2, exit_, preP2, postQ2, frameExpr, pcFreeProof, h2Expr]

  -- Permutation proof: Q1 → (P2 ** F)
  let p2StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) preP2 frameExpr
  let hperm ← mkPermLambda postQ1 p2StarFrame

  -- Compose: cpsTriple_seq_with_perm entry mid exit_ P Q1 (P2**F) (Q2**F) hperm h1 h2Framed
  let q2StarFrame := mkApp2 (mkConst ``EvmAsm.sepConj) postQ2 frameExpr
  return mkAppN (mkConst ``EvmAsm.cpsTriple_seq_with_perm)
    #[entry, mid1, exit_, preP, postQ1, p2StarFrame, q2StarFrame,
      hperm, h1Expr, h2Framed]

/-- Try to assign `result` directly to `goal`, or with a postcondition permutation. -/
def assignOrPermute (goal : MVarId) (result : Expr) : MetaM Unit := do
  let goalType ← goal.getType
  let resultType ← inferType result
  -- Attempt 1: types already match (check without side effects first)
  if ← withoutModifyingState (isDefEq goalType resultType) then
    goal.assign result
    return
  -- Attempt 2: permute postcondition via cpsTriple_consequence
  let some (gEntry, gExit, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "seqFrame: goal is not a cpsTriple"
  let some (rEntry, rExit, _, resultPost) ← parseCpsTriple? resultType
    | throwError "seqFrame: result is not a cpsTriple (internal error)"
  unless ← isDefEq gEntry rEntry do
    throwError "seqFrame: entry addresses don't match goal"
  unless ← isDefEq gExit rExit do
    throwError "seqFrame: exit addresses don't match goal"
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  let finalResult := mkAppN (mkConst ``EvmAsm.cpsTriple_consequence)
    #[gEntry, gExit, gPre, gPre, resultPost, goalPost, idPre, postPerm, result]
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
