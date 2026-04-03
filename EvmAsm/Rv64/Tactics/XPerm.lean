/-
  EvmAsm.Rv64.Tactics.XPerm

  Separation logic permutation prover for `sepConj` (`**`) chains.

  ## Usage

  ```
  -- Proves P = Q where P and Q are AC-permutations of sepConj chains
  example : (A ** B ** C) = (C ** A ** B) := by xperm
  ```

  Also used internally by `xcancel`, `seqFrame`, and `runBlock` for
  building permutation proof terms in MetaM.

  ## Key Design

  Inspired by SPlean/CFML's `xsimpl`: uses `isDefEq` for atom matching
  instead of syntactic equality (`ac_rfl`). This transparently handles
  let-bindings, type alias unfolding, and other definitional equalities.

  ## References

  - **SPlean** (Separation Logic Proofs in Lean):
    https://github.com/verse-lab/splean

  - **CFML** / Software Foundations Vol. 6:
    Arthur Charguéraud. "Separation Logic for Sequential Programs."
    https://softwarefoundations.cis.upenn.edu/slf-current/index.html
-/

import Lean
import Lean.Meta.Tactic.AC.Main
import EvmAsm.Rv64.SepLogic
import EvmAsm.Rv64.Tactics.PerfTrace

open Lean Meta Elab Tactic

namespace EvmAsm.Rv64.Tactics

/-- Normalize an expression enough to expose sepConj structure:
    - Substitute let-bound fvars (zeta)
    - Unfold @[reducible] definitions
    - Beta-reduce
    but NOT unfold sepConj/regIs/memIs/etc. (which are plain `def`s). -/
def normForSepConj (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  withReducible (whnf e)

/-- Check if an expression is `sepConj A B`, normalizing if needed.
    Returns the two arguments if so. -/
def parseSepConj? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← normForSepConj e
  if Expr.isAppOfArity e ``EvmAsm.Rv64.sepConj 2 then
    return some (Expr.appArg! (Expr.appFn! e), Expr.appArg! e)
  -- Defense-in-depth: eta-reduce `fun h => f h` to `f`, then retry
  if e.isLambda then
    let body := e.bindingBody!
    if body.isApp && body.appArg! == .bvar 0 then
      let f := body.appFn!
      if !f.hasLooseBVars then
        let f ← normForSepConj f
        if Expr.isAppOfArity f ``EvmAsm.Rv64.sepConj 2 then
          return some (Expr.appArg! (Expr.appFn! f), Expr.appArg! f)
  return none

/-- Flatten any-associated sepConj chain into a list of atoms.
    `(A ** B) ** (C ** D)` becomes `[A, B, C, D]`. -/
partial def flattenSepConj (e : Expr) : MetaM (List Expr) := do
  match ← parseSepConj? e with
  | some (l, r) => return (← flattenSepConj l) ++ (← flattenSepConj r)
  | none => return [e]

/-- Find the index of an atom in an array that is `isDefEq` to the target.
    Uses hash pre-filtering to reduce expensive `isDefEq` calls on non-matching atoms. -/
def findAtomIdx (target : Expr) (atoms : Array Expr) : MetaM (Option Nat) := do
  let h := target.hash
  -- Fast path: check atoms with matching hash first (usually O(1) bucket)
  for i in [:atoms.size] do
    if atoms[i]!.hash == h then
      if ← isDefEq target atoms[i]! then return some i
  -- Slow path: remaining atoms (handles hash mismatch + definitional equality)
  -- Uses reducible transparency to avoid deep recursion from unfolding
  -- assertion defs (memIs → singletonMem → BEq → BitVec operations).
  for i in [:atoms.size] do
    if atoms[i]!.hash != h then
      if ← withReducible (isDefEq target atoms[i]!) then return some i
  return none

/-- Remove element at `idx` from array, preserving order of remaining elements. -/
private def arrayEraseIdx (arr : Array Expr) (idx : Nat) : Array Expr := Id.run do
  let mut result : Array Expr := Array.mkEmpty (arr.size - 1)
  for i in [:arr.size] do
    if i != idx then
      result := result.push arr[i]!
  return result

/-- Build a proof that picks the element at index `k` to the front of a
    right-associated sepConj chain.

    Given chain = A₀ ** (A₁ ** (... ** (Aₖ ** ...))),
    returns `(proof, rhs)` where `proof : chain = rhs` and
    `rhs = Aₖ ** (A₀ ** (A₁ ** (...)))`.

    **Optimization**: returns the RHS expression alongside the proof,
    avoiding expensive `inferType` calls on deeply nested proof terms. -/
partial def buildPickProof (chain : Expr) (k : Nat) : MetaM (Expr × Expr) := do
  if k == 0 then
    return (← mkEqRefl chain, chain)
  else
    -- Normalize chain to expose sepConj structure
    let chainN ← normForSepConj chain
    match ← parseSepConj? chainN with
    | none => throwError "buildPickProof: expected sepConj at index {k}, got:\n{chainN}"
    | some (head, tail) =>
      let (innerProof, innerRHS) ← buildPickProof tail (k - 1)
      -- innerProof : tail = innerRHS
      let sepConjHead := mkApp (mkConst ``EvmAsm.Rv64.sepConj) head
      let step1 ← mkCongrArg sepConjHead innerProof
      -- step1 : head ** tail = head ** innerRHS
      match ← parseSepConj? innerRHS with
      | none =>
        -- Two-element case: head ** target → target ** head
        let step2 := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj_comm') head innerRHS
        let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) innerRHS head
        return (← mkEqTrans step1 step2, rhs)
      | some (target, rest) =>
        -- Three+ element case: head ** (target ** rest) → target ** (head ** rest)
        let step2 := mkApp3 (mkConst ``EvmAsm.Rv64.sepConj_left_comm') head target rest
        let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) target
          (mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) head rest)
        return (← mkEqTrans step1 step2, rhs)

/-- Reassociate a sepConj chain to right-associated form.
    Handles `(A ** B) ** C → A ** (B ** C)` recursively.
    Returns (right_assoc_expr, proof : original = right_assoc_expr).
    Uses definitional equality so proofs type-check even when the original
    expression is a let-bound fvar or other non-syntactic form. -/
partial def reassocProof (e : Expr) : MetaM (Expr × Expr) := do
  match ← parseSepConj? e with
  | none => return (e, ← mkEqRefl e)
  | some (l, r) =>
    -- Check if left side is itself a sepConj (meaning e is not right-associated here)
    match ← parseSepConj? l with
    | none =>
      -- Left is atomic, just reassociate the right subtree
      let (r', rPf) ← reassocProof r
      let newE := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) l r'
      let pf ← mkCongrArg (mkApp (mkConst ``EvmAsm.Rv64.sepConj) l) rPf
      return (newE, pf)
    | some (ll, lr) =>
      -- e =def= (ll ** lr) ** r → need to assoc to ll ** (lr ** r), then recurse
      let assocPf := mkApp3 (mkConst ``EvmAsm.Rv64.sepConj_assoc') ll lr r
      -- assocPf : (ll ** lr) ** r = ll ** (lr ** r)
      let newInner := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) lr r
      let newE := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) ll newInner
      -- Recurse (the new expression might still need reassociation)
      let (result, restPf) ← reassocProof newE
      let pf ← mkEqTrans assocPf restPf
      return (result, pf)

/-- Build proof that `chain = chain ** empAssertion` (add emp at the end).
    For `a ** (b ** c)`, returns proof: `a ** (b ** c) = a ** (b ** (c ** empAssertion))`.
    This bridges from raw sepConj chains to the `seps` representation. -/
private partial def buildAddEmpProof (chain : Expr) : MetaM (Expr × Expr) := do
  match ← parseSepConj? chain with
  | none =>
    -- Base case: single atom `x`. Prove `x = x ** empAssertion`
    let emp := mkConst ``EvmAsm.Rv64.empAssertion
    let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) chain emp
    let pf ← mkEqSymm (mkApp (mkConst ``EvmAsm.Rv64.sepConj_emp_right') chain)
    return (pf, rhs)
  | some (head, tail) =>
    -- Recursive case: `head ** tail`. Add emp to tail.
    let (tailPf, tailRhs) ← buildAddEmpProof tail
    let sepConjHead := mkApp (mkConst ``EvmAsm.Rv64.sepConj) head
    let pf ← mkCongrArg sepConjHead tailPf
    let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) head tailRhs
    return (pf, rhs)

/-- Build proof that `chain ** empAssertion = chain` (remove emp from the end).
    Inverse of `buildAddEmpProof`. -/
private partial def buildRemoveEmpProof (chain : Expr) : MetaM (Expr × Expr) := do
  match ← parseSepConj? chain with
  | none =>
    -- Shouldn't happen (chain should end with ** emp)
    return (← mkEqRefl chain, chain)
  | some (head, tail) =>
    -- Check if tail is empAssertion
    if tail == mkConst ``EvmAsm.Rv64.empAssertion then
      -- Base: `head ** emp = head`
      let pf := mkApp (mkConst ``EvmAsm.Rv64.sepConj_emp_right') head
      return (pf, head)
    else
      -- Recursive: head ** (... ** emp)
      let (tailPf, tailRhs) ← buildRemoveEmpProof tail
      let sepConjHead := mkApp (mkConst ``EvmAsm.Rv64.sepConj) head
      let pf ← mkCongrArg sepConjHead tailPf
      let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) head tailRhs
      return (pf, rhs)

/-- Build an Expr representing a `List Assertion` literal from an Array of Assertion Exprs. -/
private def mkAssertionList (atoms : Array Expr) : Expr :=
  let assertionType := mkConst ``EvmAsm.Rv64.Assertion
  atoms.foldr (init := mkApp (mkConst ``List.nil [0]) assertionType)
    fun atom acc => mkApp3 (mkConst ``List.cons [0]) assertionType atom acc

/-- Build a seps-based permutation proof: returns (proof, rhs_expr) where
    proof : seps_chain_lhs = rhs_expr, and rhs_expr is a CONCRETE sepConj chain
    (with empAssertion at the end), NOT an opaque `seps` application.

    This is the O(n)-tactic-time permutation prover. Each pick is one `seps_pick`
    application (O(1) in MetaM), vs O(k) `left_comm'` applications in the old algorithm. -/
private partial def buildSepsPermProof (lhsAtoms rhsAtoms : Array Expr) :
    MetaM (Expr × Expr) := do
  if lhsAtoms.size != rhsAtoms.size then
    throwError "buildSepsPermProof: atom count mismatch ({lhsAtoms.size} vs {rhsAtoms.size})"
  let emp := mkConst ``EvmAsm.Rv64.empAssertion
  if lhsAtoms.size == 0 then
    let pf ← mkEqRefl emp
    return (pf, emp)
  if lhsAtoms.size == 1 then
    -- seps [a] = a ** emp, rhs should also be a ** emp
    if ← isDefEq lhsAtoms[0]! rhsAtoms[0]! then
      let chain := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) lhsAtoms[0]! emp
      let pf ← mkEqRefl chain
      return (pf, chain)
    else
      throwError "buildSepsPermProof: single atoms don't match"
  -- Recursive loop: pick each RHS atom from current LHS list
  buildSepsPermAux lhsAtoms rhsAtoms 0
where
  buildSepsPermAux (currentAtoms : Array Expr) (rhsAtoms : Array Expr)
      (startIdx : Nat) : MetaM (Expr × Expr) := do
    let emp := mkConst ``EvmAsm.Rv64.empAssertion
    if startIdx >= rhsAtoms.size then
      return (← mkEqRefl emp, emp)
    if startIdx + 1 == rhsAtoms.size then
      -- Last atom: currentAtoms should have 1 element matching rhsAtoms[startIdx]
      -- The seps form is: currentAtoms[0] ** empAssertion
      if currentAtoms.size == 1 then
        if ← isDefEq currentAtoms[0]! rhsAtoms[startIdx]! then
          let chain := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) currentAtoms[0]! emp
          return (← mkEqRefl chain, chain)
        else
          throwError "buildSepsPermProof: final atoms don't match"
      else
        throwError "buildSepsPermProof: {currentAtoms.size} atoms left but only 1 RHS remaining"
    else
      let target := rhsAtoms[startIdx]!
      let some idx ← findAtomIdx target currentAtoms
        | throwError "buildSepsPermProof: could not find RHS atom {startIdx}"
      -- seps_pick proof: seps currentList = currentAtoms[idx] ** seps (eraseIdx currentList idx)
      let listExpr := mkAssertionList currentAtoms
      let idxLit := mkNatLit idx
      let boundProof ← mkDecideProof (← mkLt (mkNatLit idx) (mkNatLit currentAtoms.size))
      let pickProof := mkApp3 (mkConst ``EvmAsm.Rv64.seps_pick) listExpr idxLit boundProof
      -- Recurse on tail
      let newAtoms := (currentAtoms.extract 0 idx) ++ (currentAtoms.extract (idx + 1) currentAtoms.size)
      let (tailProof, tailRhs) ← buildSepsPermAux newAtoms rhsAtoms (startIdx + 1)
      -- tailProof : seps newAtoms = tailRhs (concrete chain)
      -- Build: target ** seps newAtoms = target ** tailRhs
      let sepConjTarget := mkApp (mkConst ``EvmAsm.Rv64.sepConj) target
      let step2 ← mkCongrArg sepConjTarget tailProof
      let rhs := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) target tailRhs
      -- Chain: seps currentList = target ** seps newAtoms = target ** tailRhs
      let pf ← mkEqTrans pickProof step2
      return (pf, rhs)

/-- Check if two sepConj chains are eligible for AC normalization.
    Requires: both are sepConj chains with ≥2 atoms, and sorted atom hashes match. -/
private def checkACEligible (lhs rhs : Expr) : MetaM Bool := do
  let lAtoms ← flattenSepConj lhs
  let rAtoms ← flattenSepConj rhs
  if lAtoms.length != rAtoms.length then return false
  if lAtoms.length < 2 then return false
  let lHashes := lAtoms.map (·.hash) |>.toArray |>.insertionSort (· < ·)
  let rHashes := rAtoms.map (·.hash) |>.toArray |>.insertionSort (· < ·)
  for i in [:lHashes.size] do
    if lHashes[i]! != rHashes[i]! then return false
  return true

/-- Report which atoms differ between LHS and RHS (for diagnostics). -/
private def reportAtomMismatches (lhsAtoms rhsAtoms : List Expr) : MetaM MessageData := do
  let la := lhsAtoms.toArray
  let ra := rhsAtoms.toArray
  let lHashes := la.map (·.hash)
  let rHashSet := Std.HashSet.ofArray (ra.map (·.hash))
  let lHashSet := Std.HashSet.ofArray lHashes
  let mut msgs : Array MessageData := #[]
  for i in [:la.size] do
    unless rHashSet.contains la[i]!.hash do
      msgs := msgs.push m!"  LHS atom {i} (hash {la[i]!.hash}): {la[i]!}"
  for i in [:ra.size] do
    unless lHashSet.contains ra[i]!.hash do
      msgs := msgs.push m!"  RHS atom {i} (hash {ra[i]!.hash}): {ra[i]!}"
  return MessageData.joinSep msgs.toList "\n"

/-- The main permutation proof builder.

    Given LHS and RHS as sepConj chains with the same atoms
    (syntactically identical), builds a proof of `LHS = RHS`.

    Uses AC reflection via `buildNormProof` for O(n log n) kernel work.
    If atoms are not syntactically identical (different Expr.hash), reports
    the mismatching atoms so the caller can fix the normalization. -/
partial def buildPermProof (lhs rhs : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.perm (fun _ => return m!"perm") do
  let lhsAtoms ← flattenSepConj lhs
  let rhsAtoms ← flattenSepConj rhs
  -- Check atom count
  unless lhsAtoms.length == rhsAtoms.length do
    throwError "xperm: atom count mismatch ({lhsAtoms.length} LHS vs {rhsAtoms.length} RHS)"
  -- Handle trivial cases (0-1 atoms): just check isDefEq
  if lhsAtoms.length ≤ 1 then
    if ← isDefEq lhs rhs then
      return ← mkEqRefl lhs
    else
      throwError "xperm: single atom doesn't match:\n  LHS: {lhs}\n  RHS: {rhs}"
  -- Check sorted hashes match (atoms must be syntactically identical)
  let acEligible ← checkACEligible lhs rhs
  unless acEligible do
    let diffs ← reportAtomMismatches lhsAtoms rhsAtoms
    throwError "xperm: atoms are not syntactically identical (different Expr.hash).\n\
      Both sides have {lhsAtoms.length} atoms but some differ structurally.\n\
      Mismatching atoms:\n{diffs}\n\n\
      Hint: ensure both sides use the same representation for addresses \
      (e.g., normalize signExtend12 before calling xperm)."
  -- AC reflection: normalize each side, check normal forms match
  let op := mkConst ``EvmAsm.Rv64.sepConj
  let some pc ← Lean.Meta.AC.preContext op
    | throwError "xperm: sepConj has no Associative/Commutative instances"
  let some (lHead, lTail) ← parseSepConj? lhs
    | throwError "xperm: LHS is not a sepConj chain"
  let some (rHead, rTail) ← parseSepConj? rhs
    | throwError "xperm: RHS is not a sepConj chain"
  let (lPf, lNorm) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 1024 }) do
    Lean.Meta.AC.buildNormProof pc lHead lTail
  let (rPf, rNorm) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 1024 }) do
    Lean.Meta.AC.buildNormProof pc rHead rTail
  unless ← isDefEq lNorm rNorm do
    throwError "xperm: AC normal forms differ (atoms matched by hash but not by AC normalization)"
  mkEqTrans lPf (← mkEqSymm rPf)

/-- `xperm` tactic: proves `⊢ P = Q` where P and Q are AC-permutations of
    sepConj chains, using `isDefEq` for atom matching. -/
elab "xperm" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, lhsExpr, rhsExpr) := Expr.eq? goalType
    | throwError "xperm: goal is not an equality, got:\n{goalType}"
  let proof ← buildPermProof lhsExpr rhsExpr
  goal.assign proof

end EvmAsm.Rv64.Tactics
