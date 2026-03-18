/-
  EvmAsm.Rv64.Tactics.SeqFrame

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
import EvmAsm.Rv64.Tactics.XCancel
import EvmAsm.Rv64.InstructionSpecs
import EvmAsm.Rv64.Tactics.PerfTrace

open Lean Meta Elab Tactic

namespace EvmAsm.Rv64.Tactics

/-- Run a tactic without leaking error diagnostics on failure.
    Saves the message log before running, restores it if the tactic throws.
    This prevents speculative tactic calls (e.g., bv_omega in try/catch blocks)
    from polluting the error output when they fail as expected. -/
def runTacticSilent (mvarId : MVarId) (stx : Syntax) : MetaM Unit := do
  let savedLog ← Lean.Core.getMessageLog
  Lean.Core.resetMessageLog
  try
    let _ ← Lean.Elab.runTactic mvarId stx
    let newLog ← Lean.Core.getMessageLog
    Lean.Core.setMessageLog (savedLog ++ newLog)
  catch e =>
    Lean.Core.setMessageLog savedLog
    throw e

/-- Parse `cpsTriple entry exit_ cr P Q` returning the five arguments.
    Does NOT whnf (which would unfold the def). -/
def parseCpsTriple? (e : Expr) : MetaM (Option (Expr × Expr × Expr × Expr × Expr)) := do
  let e ← instantiateMVars e
  -- First try without whnf (fast path)
  if e.isAppOfArity ``EvmAsm.Rv64.cpsTriple 5 then
    let args := e.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  -- Try zetaReduce to resolve let-bindings without unfolding defs or normalizing addresses
  let e' ← Lean.Meta.zetaReduce e
  if e'.isAppOfArity ``EvmAsm.Rv64.cpsTriple 5 then
    let args := e'.getAppArgs
    return some (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  return none

/-- Given Q1 (postcondition of h1) and P2 (precondition of h2),
    find atoms of P2 within Q1 and return the frame (residual Q1 atoms).
    Both sides are first reassociated to right-associated form for proper flattening.
    Uses hash pre-filtering to reduce expensive `isDefEq` calls. -/
def computeFrame (q1 p2 : Expr) : MetaM (List Expr) :=
  withTraceNode `runBlock.perf.frame (fun _ => return m!"computeFrame") do
  -- Reassociate to right-associated form before flattening
  let (q1RA, _) ← reassocProof q1
  let (p2RA, _) ← reassocProof p2
  let q1Atoms := (← flattenSepConj q1RA).toArray
  let p2Atoms := (← flattenSepConj p2RA).toArray
  -- Filter out empAssertion atoms (identity for **; no matching needed)
  let p2Atoms := p2Atoms.filter fun a => !(a == mkConst ``EvmAsm.Rv64.empAssertion)
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
    -- Uses reducible transparency to avoid deep recursion from unfolding
    -- assertion defs (memIs → singletonMem → BEq → BitVec operations).
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

/-- Check if an expression is a numeric literal (OfNat.ofNat _ n _) and return n. -/
private def getBvLitVal? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.getAppArgs[1]! with
    | .lit (.natVal n) => some n
    | _ => none
  else none

/-- Extract base and numeric offset from an address expression.
    - `base + lit` → `some (base, some lit_expr, lit_val)`
    - bare `e` → `some (e, none, 0)`
    - unrecognized → `none` -/
private def extractBaseAndOffset (e : Expr) : Option (Expr × Option Expr × Nat) :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let rhs := e.getAppArgs[5]!
    if let some k := getBvLitVal? rhs then
      some (e.getAppArgs[4]!, some rhs, k)
    else
      none
  else
    some (e, none, 0)

/-- Prove `a1 ≠ a2` using offset-based reflection when both addresses share the same base.
    Falls back to `bv_omega` when the pattern doesn't match.
    ~100x faster than bv_omega for the common case (base + k1 ≠ base + k2). -/
private def proveAddrNe (a1 a2 : Expr) : MetaM Expr := do
  let addrType := mkConst ``EvmAsm.Rv64.Addr
  -- Try offset-based fast path
  if let some (base1, off1, k1) := extractBaseAndOffset a1 then
    if let some (base2, off2, k2) := extractBaseAndOffset a2 then
      if base1 == base2 then
        try
          match off1, off2 with
          | some k1Bv, some k2Bv =>
            -- base + k1 ≠ base + k2
            if k1 != k2 then
              let neType := mkApp3 (mkConst ``Ne [levelOne]) addrType k1Bv k2Bv
              let hne ← mkDecideProof neType
              return mkApp4 (mkConst ``EvmAsm.Rv64.addr_ne_of_bv_ne) base1 k1Bv k2Bv hne
          | none, some kBv =>
            -- base ≠ base + k
            let bv64Type := mkApp (mkConst ``BitVec) (mkNatLit 64)
            let zeroAddr ← mkNumeral bv64Type 0
            let neType := mkApp3 (mkConst ``Ne [levelOne]) addrType kBv zeroAddr
            let hne ← mkDecideProof neType
            return mkApp3 (mkConst ``EvmAsm.Rv64.addr_ne_add_right) base1 kBv hne
          | some kBv, none =>
            -- base + k ≠ base
            let bv64Type := mkApp (mkConst ``BitVec) (mkNatLit 64)
            let zeroAddr ← mkNumeral bv64Type 0
            let neType := mkApp3 (mkConst ``Ne [levelOne]) addrType kBv zeroAddr
            let hne ← mkDecideProof neType
            return mkApp3 (mkConst ``EvmAsm.Rv64.addr_add_ne_left) base1 kBv hne
          | none, none => (Pure.pure PUnit.unit : MetaM PUnit)
        catch _ => (Pure.pure PUnit.unit : MetaM PUnit)
  -- Fallback: bv_omega
  let neqType := mkApp3 (mkConst ``Ne [levelOne]) addrType a1 a2
  let neqMVar ← mkFreshExprMVar neqType
  let stx ← `(tactic| bv_omega)
  runTacticSilent neqMVar.mvarId! stx
  instantiateMVars neqMVar

/-- Build a `pcFree` proof directly in MetaM, avoiding tactic overhead.
    Handles all standard assertion types; falls back to the `pcFree` tactic for unknowns. -/
partial def buildPcFreeProof (assertion : Expr) : MetaM Expr := do
  let e ← normForSepConj assertion
  if e.isAppOfArity ``EvmAsm.Rv64.sepConj 2 then
    let l := Expr.appArg! (Expr.appFn! e)
    let r := Expr.appArg! e
    let lPf ← buildPcFreeProof l
    let rPf ← buildPcFreeProof r
    return mkApp4 (mkConst ``EvmAsm.Rv64.pcFree_sepConj) l r lPf rPf
  else if e.isAppOfArity `EvmAsm.Rv64.instrAt 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.Rv64.pcFree_instrAt) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.Rv64.regIs 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.Rv64.pcFree_regIs) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.Rv64.memIs 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.Rv64.pcFree_memIs) args[0]! args[1]!
  else if e.isAppOfArity `EvmAsm.Rv64.regOwn 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_regOwn) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.Rv64.memOwn 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_memOwn) e.getAppArgs[0]!
  else if e == mkConst ``EvmAsm.Rv64.empAssertion then
    return mkConst ``EvmAsm.Rv64.pcFree_emp
  else if e.isAppOfArity `EvmAsm.Rv64.pure 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_pure) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.Rv64.publicValuesIs 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_publicValuesIs) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.Rv64.privateInputIs 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_privateInputIs) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.Rv64.programAt 1 then
    return mkApp (mkConst ``EvmAsm.Rv64.pcFree_programAt) e.getAppArgs[0]!
  else if e.isAppOfArity `EvmAsm.Rv64.progAt 2 then
    let args := e.getAppArgs
    return mkApp2 (mkConst ``EvmAsm.Rv64.pcFree_progAt) args[0]! args[1]!
  else
    -- Fallback to tactic for unknown assertion types
    let pcFreeType := mkApp (mkConst ``EvmAsm.Rv64.Assertion.pcFree) assertion
    let pcFreeMVar ← mkFreshExprMVar pcFreeType
    let stx ← `(tactic| pcFree)
    let _ ← Lean.Elab.runTactic pcFreeMVar.mvarId! stx
    instantiateMVars pcFreeMVar

/-- Build a lambda `fun (h : PartialState) (hp : P h) => proof h hp`
    where proof converts `P h` to `Q h` using a permutation equality `P = Q`. -/
def mkPermLambda (src tgt : Expr) : MetaM Expr := do
  let permProof ← buildPermProof src tgt
  let psType := mkConst ``EvmAsm.Rv64.PartialState
  withLocalDeclD `h psType fun h => do
    withLocalDeclD `hp (mkApp src h) fun hp => do
      let proof ← mkEqMP (← mkCongrFun permProof h) hp
      mkLambdaFVars #[h, hp] proof

/-- Build identity lambda: `fun (h : PartialState) (hp : P h) => hp` -/
def mkIdLambda (p : Expr) : MetaM Expr := do
  let psType := mkConst ``EvmAsm.Rv64.PartialState
  withLocalDeclD `h psType fun h =>
    withLocalDeclD `hp (mkApp p h) fun hp =>
      mkLambdaFVars #[h, hp] hp

/-- Build a proof of `CodeReq.Disjoint cr1 cr2` by structural recursion on cr1, cr2.
    Handles the common cases:
    - empty vs anything
    - singleton vs singleton (uses bv_omega to prove addresses differ)
    - union vs anything (recursive)
    Falls back to the `decide` tactic for unknown structures. -/
partial def buildDisjointProof (cr1 cr2 : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.extend (fun _ => return m!"buildDisjointProof") do
  let cr1 ← whnfR cr1
  let cr2 ← whnfR cr2
  -- Case: cr1 = empty
  if cr1 == mkConst ``EvmAsm.Rv64.CodeReq.empty then
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.Disjoint.empty_left #[cr2]
  -- Case: cr2 = empty
  if cr2 == mkConst ``EvmAsm.Rv64.CodeReq.empty then
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.Disjoint.empty_right #[cr1]
  -- Case: cr1 = singleton a1 i1, cr2 = singleton a2 i2
  if cr1.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 &&
     cr2.isAppOfArity ``EvmAsm.Rv64.CodeReq.singleton 2 then
    let a1 := cr1.getAppArgs[0]!
    let i1 := cr1.getAppArgs[1]!
    let a2 := cr2.getAppArgs[0]!
    let i2 := cr2.getAppArgs[1]!
    -- Quick check: if addresses are definitionally equal, cannot prove disjoint
    if ← withoutModifyingState (isDefEq a1 a2) then
      throwError "buildDisjointProof: addresses are equal: {a1}"
    -- Prove a1 ≠ a2 (fast offset-based when possible, bv_omega fallback)
    let neqProof ← proveAddrNe a1 a2
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.Disjoint.singleton #[neqProof, i1, i2]
  -- Case: cr1 = union sub1 sub2 → need sub1.Disjoint cr2 and sub2.Disjoint cr2
  if cr1.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let sub1 := cr1.getAppArgs[0]!
    let sub2 := cr1.getAppArgs[1]!
    let hd1 ← buildDisjointProof sub1 cr2
    let hd2 ← buildDisjointProof sub2 cr2
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.Disjoint.union_left #[hd1, hd2]
  -- Case: cr2 = union sub1 sub2 → need cr1.Disjoint sub1 and cr1.Disjoint sub2
  if cr2.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let sub1 := cr2.getAppArgs[0]!
    let sub2 := cr2.getAppArgs[1]!
    let hd1 ← buildDisjointProof cr1 sub1
    let hd2 ← buildDisjointProof cr1 sub2
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.Disjoint.union_right #[hd1, hd2]
  -- Fallback: try native_decide
  let disjType := mkApp2 (mkConst ``EvmAsm.Rv64.CodeReq.Disjoint) cr1 cr2
  let disjMVar ← mkFreshExprMVar disjType
  let stx ← `(tactic| intro a; simp [CodeReq.singleton, CodeReq.union, CodeReq.empty]; decide)
  try
    runTacticSilent disjMVar.mvarId! stx
    return ← instantiateMVars disjMVar
  catch _ =>
    throwError "seqFrame: cannot prove CodeReq.Disjoint for:\n  cr1 = {cr1}\n  cr2 = {cr2}"

/-- Build identity monotonicity proof: `fun a i h => h` (for same-CR extension). -/
def mkIdentityMono (cr : Expr) : MetaM Expr := do
  let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let instrType := mkConst ``EvmAsm.Rv64.Instr
  withLocalDeclD `a bv64 fun a =>
    withLocalDeclD `i instrType fun i => do
      let someI ← mkAppOptM ``some #[instrType, i]
      let eqType ← mkEq (mkApp cr a) someI
      withLocalDeclD `h eqType fun h =>
        mkLambdaFVars #[a, i, h] h

/-- Fallback: Build monotonicity proof via tactic (for edge cases). -/
private def buildMonoProofTactic (oldCr newCr : Expr) : MetaM Expr := do
  let bv64 := mkApp (mkConst ``BitVec) (mkNatLit 64)
  let instrType := mkConst ``EvmAsm.Rv64.Instr
  let propType ← withLocalDeclD `a bv64 fun a => do
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
    let stx ← `(tactic| intro a i h; simp only [EvmAsm.Rv64.CodeReq.singleton, EvmAsm.Rv64.CodeReq.union] at *; (first | simp_all | (split at h <;> simp_all <;> bv_omega)))
    runTacticSilent mvar.mvarId! stx
    return ← instantiateMVars mvar
  catch _ =>
    throwError "seqFrame: cannot build monotonicity proof for CodeReq extension (fallback)"

/-- Build a proof of `∀ a i, oldCr a = some i → newCr a = some i` structurally.
    Walks the union chain to find matching pieces, composing with
    CodeReq.union_mono_left, mono_union_right, and union_split_mono.
    Falls back to tactic-based proof for edge cases. -/
partial def buildMonoProof (oldCr newCr : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.extend (fun _ => return m!"buildMonoProof") do
  -- Identity: oldCr ≡ newCr
  if oldCr == newCr then return ← mkIdentityMono oldCr
  if ← withoutModifyingState (withReducible (isDefEq oldCr newCr)) then
    return ← mkIdentityMono oldCr
  let oldCrW ← whnfR oldCr
  let newCrW ← whnfR newCr
  -- newCr = union(head, tail): walk the chain
  -- Check this BEFORE splitting oldCr so that an opaque abbrev (e.g., mul_col0_code base)
  -- can match a head in newCr's chain without being expanded first.
  if newCrW.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let head := newCrW.getAppArgs[0]!
    let tail := newCrW.getAppArgs[1]!
    -- Left match: oldCr ≡ head (pre-whnfR, preserving abbrev identity)
    if oldCr == head then
      return ← mkAppM ``EvmAsm.Rv64.CodeReq.union_mono_left #[head, tail]
    if ← withoutModifyingState (withReducible (isDefEq oldCr head)) then
      return ← mkAppM ``EvmAsm.Rv64.CodeReq.union_mono_left #[head, tail]
    -- Also check whnfR'd form (handles case where oldCr was already expanded)
    if oldCrW == head then
      return ← mkAppM ``EvmAsm.Rv64.CodeReq.union_mono_left #[head, tail]
    if ← withoutModifyingState (withReducible (isDefEq oldCrW head)) then
      return ← mkAppM ``EvmAsm.Rv64.CodeReq.union_mono_left #[head, tail]
    -- No head match. Try skip (prove head.Disjoint oldCr, recurse on tail) first,
    -- then fall back to splitting oldCr. The skip-first order is essential when oldCr
    -- is an opaque abbrev that will match a LATER head in newCr's chain — splitting
    -- would expand it into singletons that can't match the unexpanded abbrev heads.
    try
      let disjProof ← buildDisjointProof head oldCr
      let tailMono ← buildMonoProof oldCr tail
      return ← mkAppM ``EvmAsm.Rv64.CodeReq.mono_union_right #[disjProof, tailMono]
    catch _ =>
      -- Skip failed (disjointness unprovable); fall through to split oldCr below
      (Pure.pure PUnit.unit : MetaM PUnit)
  -- oldCr = union(sub1, sub2): split and recurse
  if oldCrW.isAppOfArity ``EvmAsm.Rv64.CodeReq.union 2 then
    let sub1 := oldCrW.getAppArgs[0]!
    let sub2 := oldCrW.getAppArgs[1]!
    let headMono ← buildMonoProof sub1 newCr
    let tailMono ← buildMonoProof sub2 newCr
    return ← mkAppM ``EvmAsm.Rv64.CodeReq.union_split_mono #[headMono, tailMono]
  -- Fallback: tactic-based proof
  buildMonoProofTactic oldCr newCr

/-- Extend a spec's CodeReq from oldCr to newCr using `cpsTriple_extend_code`. -/
def extendSpecCr (spec : Expr) (oldCr newCr : Expr) : MetaM Expr := do
  if oldCr == newCr then return spec
  if ← withoutModifyingState (withReducible (isDefEq oldCr newCr)) then return spec
  let monoProof ← buildMonoProof oldCr newCr
  mkAppM ``EvmAsm.Rv64.cpsTriple_extend_code #[monoProof, spec]

/-- Core MetaM implementation of seqFrame.
    Returns the composed proof term. -/
def seqFrameCore (h1Expr h2Expr : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.seq (fun _ => return m!"seqFrameCore") do
  let h1Type ← inferType h1Expr
  let h2Type ← inferType h2Expr

  let some (entry, mid1, cr1, preP, postQ1) ← parseCpsTriple? h1Type
    | throwError "seqFrame: first argument is not a cpsTriple"
  let some (mid2, exit_, cr2, preP2, postQ2) ← parseCpsTriple? h2Type
    | throwError "seqFrame: second argument is not a cpsTriple"

  unless ← isDefEq mid1 mid2 do
    throwError "seqFrame: midpoints don't match:\n  h1 exit: {mid1}\n  h2 entry: {mid2}"

  -- Check if P2 is empAssertion (e.g., jal_x0_spec_gen).
  -- When P2 = empAssertion, the spec needs no state atoms. We frame h2 with Q1,
  -- then use cpsTriple_consequence with sepConj_emp_left' to eliminate empAssertion.
  let preP2N ← normForSepConj preP2
  let p2IsEmp := preP2N == mkConst ``EvmAsm.Rv64.empAssertion

  -- Find frame: Q1 atoms not matched by P2
  let frameAtoms ← computeFrame postQ1 preP2

  if frameAtoms.isEmpty then
    -- No frame: compose directly with permutation (avoids spurious empAssertion atom)
    let hperm ← mkPermLambda postQ1 preP2
    -- Same-CR fast path
    if ← withoutModifyingState (isDefEq cr1 cr2) then
      return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm_same_cr)
        #[entry, mid1, exit_, cr1, preP, postQ1, preP2, postQ2,
          hperm, h1Expr, h2Expr]
    -- Different CRs
    let hdProof ← buildDisjointProof cr1 cr2
    return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm)
      #[entry, mid1, exit_, cr1, cr2, hdProof, preP, postQ1, preP2, postQ2,
        hperm, h1Expr, h2Expr]

  let frameExpr ← buildSepConjChain frameAtoms

  -- Solve pcFree for the frame (direct proof construction, no tactic overhead)
  let pcFreeProof ← try buildPcFreeProof frameExpr
    catch _ => throwError "seqFrame: could not prove pcFree for frame:\n  {frameExpr}"

  -- h2Framed : cpsTriple mid exit_ cr2 (P2 ** F) (Q2 ** F)
  let h2Framed := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_frame_left)
    #[mid2, exit_, cr2, preP2, postQ2, frameExpr, pcFreeProof, h2Expr]

  -- When P2 = empAssertion, simplify (empAssertion ** F) to F and (Q2 ** F) similarly.
  -- Uses cpsTriple_consequence with sepConj_emp_left' to eliminate empAssertion.
  if p2IsEmp then
    -- Build pre-simplification: empAssertion ** F → F
    -- hpre : F → empAssertion ** F (reverse direction for consequence pre)
    let empStarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) preP2 frameExpr
    let preRw := mkApp (mkConst ``EvmAsm.Rv64.sepConj_emp_left') frameExpr
    -- preRw : empAssertion ** F = F
    -- We need hpre : F → empAssertion ** F, i.e., λ h hp => (preRw.symm ▸ hp)
    let psType := mkConst ``EvmAsm.Rv64.PartialState
    let hpre ← withLocalDeclD `h psType fun h => do
      withLocalDeclD `hp (mkApp frameExpr h) fun hp => do
        -- Eq.mp (congrFun preRw.symm h) hp : (empAssertion ** F) h
        let congrPf ← mkCongrFun (← mkEqSymm preRw) h
        let result ← mkEqMP congrPf hp
        mkLambdaFVars #[h, hp] result
    -- Build post-simplification: Q2 ** F → F (when Q2 = empAssertion too)
    let postQ2N ← normForSepConj postQ2
    let q2IsEmp := postQ2N == mkConst ``EvmAsm.Rv64.empAssertion
    let q2StarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) postQ2 frameExpr
    let (actualPost, hpost) ← if q2IsEmp then do
      -- hpost : empAssertion ** F → F
      let postRw := mkApp (mkConst ``EvmAsm.Rv64.sepConj_emp_left') frameExpr
      let hpost ← withLocalDeclD `h psType fun h => do
        withLocalDeclD `hq (mkApp q2StarFrame h) fun hq => do
          let congrPf ← mkCongrFun postRw h
          let result ← mkEqMP congrPf hq
          mkLambdaFVars #[h, hq] result
      Pure.pure (frameExpr, hpost)
    else do
      let hpost ← mkIdLambda q2StarFrame
      Pure.pure (q2StarFrame, hpost)
    -- h2Simplified : cpsTriple mid exit_ cr2 F actualPost
    let h2Simplified := mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_consequence)
      #[mid2, exit_, cr2, empStarFrame, frameExpr, q2StarFrame, actualPost,
        hpre, hpost, h2Framed]
    -- Permutation: Q1 = F (since frame = all Q1 atoms)
    let hperm ← mkPermLambda postQ1 frameExpr
    -- Same-CR fast path
    if ← withoutModifyingState (isDefEq cr1 cr2) then
      return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm_same_cr)
        #[entry, mid1, exit_, cr1, preP, postQ1, frameExpr, actualPost,
          hperm, h1Expr, h2Simplified]
    -- Different CRs
    let hdProof ← buildDisjointProof cr1 cr2
    return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm)
      #[entry, mid1, exit_, cr1, cr2, hdProof, preP, postQ1, frameExpr, actualPost,
        hperm, h1Expr, h2Simplified]

  -- Permutation proof: Q1 → (P2 ** F)
  let p2StarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) preP2 frameExpr
  let hperm ← mkPermLambda postQ1 p2StarFrame

  let q2StarFrame := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) postQ2 frameExpr

  -- Same-CR fast path: skip disjointness proof
  if ← withoutModifyingState (isDefEq cr1 cr2) then
    return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm_same_cr)
      #[entry, mid1, exit_, cr1, preP, postQ1, p2StarFrame, q2StarFrame,
        hperm, h1Expr, h2Framed]

  -- Different CRs: build disjointness proof
  let hdProof ← buildDisjointProof cr1 cr2

  -- Compose: cpsTriple_seq_with_perm entry mid exit_ cr1 cr2 hd P Q1 (P2**F) (Q2**F) hperm h1 h2Framed
  return mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_seq_with_perm)
    #[entry, mid1, exit_, cr1, cr2, hdProof, preP, postQ1, p2StarFrame, q2StarFrame,
      hperm, h1Expr, h2Framed]

/-- Try to assign `result` directly to `goal`, or with a postcondition permutation. -/
def assignOrPermute (goal : MVarId) (result : Expr) : MetaM Unit := do
  let goalType ← goal.getType
  let resultType ← inferType result
  -- Attempt 1: types already match (check without side effects first)
  if ← withoutModifyingState (isDefEq goalType resultType) then
    goal.assign result
    return
  -- Attempt 2: permute postcondition (and extend CR if needed) via cpsTriple_consequence
  let some (gEntry, gExit, gCr, gPre, goalPost) ← parseCpsTriple? goalType
    | throwError "seqFrame: goal is not a cpsTriple"
  let some (rEntry, rExit, rCr, _, resultPost) ← parseCpsTriple? resultType
    | throwError "seqFrame: result is not a cpsTriple (internal error)"
  unless ← isDefEq gEntry rEntry do
    throwError "seqFrame: entry addresses don't match goal"
  unless ← isDefEq gExit rExit do
    throwError "seqFrame: exit addresses don't match goal"
  -- If CRs differ, extend the result's CR to the goal's CR first
  let result' ←
    if ← withoutModifyingState (isDefEq gCr rCr) then
      Pure.pure result
    else do
      -- Build monotonicity proof: rCr ⊆ gCr
      let monoProof ← try buildMonoProof rCr gCr
        catch e =>
          Lean.logInfo m!"seqFrame/assignOrPermute: CR extension failed:\n  rCr = {rCr}\n  gCr = {gCr}\n  error = {← e.toMessageData.toString}"
          throw e
      -- Extend result's CR: cpsTriple_extend_code monoProof result
      let extended ← mkAppM ``EvmAsm.Rv64.cpsTriple_extend_code #[monoProof, result]
      Pure.pure extended
  let postPerm ← mkPermLambda resultPost goalPost
  let idPre ← mkIdLambda gPre
  goal.assign (mkAppN (mkConst ``EvmAsm.Rv64.cpsTriple_consequence)
    #[gEntry, gExit, gCr, gPre, gPre, resultPost, goalPost, idPre, postPerm, result'])

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
  catch e =>
    Lean.logWarning m!"seqFrame: could not close goal: {← e.toMessageData.toString}"
    -- Introduce as a named hypothesis
    let name := Name.mkSimple s!"{h1.getId}{h2.getId}"
    let fvarId ← liftMetaTacticAux (α := FVarId) fun mvarId => do
      let (fvarId, mvarId) ← mvarId.note name result
      return (fvarId, [mvarId])
    -- Register name in elaboration context so subsequent tactics can find it
    withMainContext do
      Term.addLocalVarInfo (mkIdent name) (.fvar fvarId)

/-- `crMono` proves a goal of the form `∀ a i, cr1 a = some i → cr2 a = some i`
    by structural recursion on union/singleton trees. -/
elab "crMono" : tactic => do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let goalType ← whnfR goalType
  -- Extract cr1 and cr2 from ∀ a i, cr1 a = some i → cr2 a = some i
  -- The type should be a pi: ∀ (a : Addr) (i : Instr), cr1 a = some i → cr2 a = some i
  -- buildMonoProof handles this structurally
  -- Fall back to tactic: intro a i h; simp ... at h ⊢; split at h <;> simp_all <;> bv_omega
  let stx ← `(tactic| intro a i h; simp only [EvmAsm.Rv64.CodeReq.singleton, EvmAsm.Rv64.CodeReq.union] at *; (first | simp_all | (split at h <;> simp_all <;> bv_omega)))
  let _ ← Lean.Elab.runTactic goal stx
  replaceMainGoal []

/-- `crDisjoint` proves a goal of the form `CodeReq.Disjoint cr1 cr2`
    by structural recursion on union/singleton, using bv_omega for address inequality. -/
elab "crDisjoint" : tactic => do
  let goal ← getMainGoal
  let goalType ← instantiateMVars (← goal.getType)
  let goalType ← whnfR goalType
  -- Extract cr1 and cr2 from CodeReq.Disjoint cr1 cr2
  -- The goal may appear as CodeReq.Disjoint cr1 cr2 (fully qualified)
  -- or as cr1.Disjoint cr2 (dot notation → same Expr structure)
  unless goalType.isAppOfArity ``EvmAsm.Rv64.CodeReq.Disjoint 2 do
    throwError "crDisjoint: goal is not a CodeReq.Disjoint, got:\n  {goalType}"
  let cr1 := goalType.getAppArgs[0]!
  let cr2 := goalType.getAppArgs[1]!
  let proof ← buildDisjointProof cr1 cr2
  goal.assign proof
  replaceMainGoal []

end EvmAsm.Rv64.Tactics
