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

/-- PoC A/B switch: when `true`, the `xperm` family (`xperm`, `xperm_hyp`,
    `xcancel`, `seqFrame`/`runBlock` postcondition permutations, `xsimp`) builds
    its `sepConj`-permutation proofs via the YOLO-style certificate prover
    (`buildPermProofCert`) instead of the default `buildPermProof`. Default
    `false` keeps the baseline behaviour byte-for-byte unchanged. -/
register_option xperm.cert : Bool := {
  defValue := true
  descr := "Use the certificate-based sepConj permutation prover (seps_permute)."
}

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

/-- Normalize an atom for hash comparison: recursively whnf with reducible
    transparency to normalize OfNat instances and Fin proof terms.
    Skips subexpressions with loose bound variables to avoid WHNF panics. -/
private def normalizeAtomForHash (e : Expr) : MetaM Expr :=
  Lean.Core.transform e (pre := fun sub => do
    if sub.hasLooseBVars then return .continue
    let sub' ← withReducible (whnf sub)
    if sub' == sub then return .continue
    else return .continue sub')

/-- Check if two sepConj chains are eligible for AC normalization.
    Requires: both are sepConj chains with ≥2 atoms, and sorted atom hashes match
    after reducible normalization. -/
private def checkACEligible (lhs rhs : Expr) : MetaM Bool := do
  let lAtoms ← flattenSepConj lhs
  let rAtoms ← flattenSepConj rhs
  if lAtoms.length != rAtoms.length then return false
  if lAtoms.length < 2 then return false
  let lNorm ← lAtoms.mapM normalizeAtomForHash
  let rNorm ← rAtoms.mapM normalizeAtomForHash
  let lHashes := lNorm.map (·.hash) |>.toArray |>.insertionSort (· < ·)
  let rHashes := rNorm.map (·.hash) |>.toArray |>.insertionSort (· < ·)
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

/-- Fallback pick-based permutation prover (O(n^2) in atom count).
    Used when AC reflection is not safe (e.g., expressions with loose bvars). -/
private partial def buildPermProofFallback (lhs rhs : Expr) : MetaM Expr := do
  -- First reassociate both sides to right-associated form
  let (lhsRA, lhsPf) ← reassocProof lhs
  let (rhsRA, rhsPf) ← reassocProof rhs
  -- Flatten LHS once (not per-atom)
  let lhsAtoms := (← flattenSepConj lhsRA).toArray
  let rhsAtoms := (← flattenSepConj rhsRA).toArray
  -- Build permutation proof on right-associated forms
  let permPf ← buildPermProofPickAux lhsRA lhsAtoms rhsAtoms
  -- Chain: lhs = lhsRA = rhsRA = rhs
  let step1 ← mkEqTrans lhsPf permPf
  let rhsPfSymm ← mkEqSymm rhsPf
  mkEqTrans step1 rhsPfSymm
where
  /-- Inner loop: pick each RHS atom from the LHS chain. -/
  buildPermProofPickAux (currentLhs : Expr) (lhsAtoms : Array Expr)
      (remainingRhs : Array Expr) (startIdx : Nat := 0) : MetaM Expr := do
    if startIdx >= remainingRhs.size then
      mkEqRefl currentLhs
    else if startIdx + 1 == remainingRhs.size then
      let target := remainingRhs[startIdx]!
      if lhsAtoms.size == 1 then
        if ← isDefEq currentLhs target then
          mkEqRefl currentLhs
        else
          throwError "xperm: final atoms don't match:\n  LHS: {currentLhs}\n  RHS: {target}"
      else
        throwError "xperm: LHS has {lhsAtoms.size} atoms but only 1 remaining in RHS"
    else
      let target := remainingRhs[startIdx]!
      let some idx ← findAtomIdx target lhsAtoms
        | throwError "xperm: could not find atom in LHS matching RHS atom:\n  target: {target}\n  LHS ({lhsAtoms.size} atoms)"
      let (pickProof, pickedRhs) ← buildPickProof currentLhs idx
      match ← parseSepConj? pickedRhs with
      | none =>
        throwError "xperm: picked result is a single atom but {remainingRhs.size - startIdx} RHS atoms remain"
      | some (pickedHead, pickedTail) =>
        let newLhsAtoms := arrayEraseIdx lhsAtoms idx
        let tailProof ← buildPermProofPickAux pickedTail newLhsAtoms remainingRhs (startIdx + 1)
        let sepConjPicked := mkApp (mkConst ``EvmAsm.Rv64.sepConj) pickedHead
        let step2 ← mkCongrArg sepConjPicked tailProof
        mkEqTrans pickProof step2

/-- The AC-reflection fast path, extracted from `buildPermProof` so other
    routes (the certificate prover) can try it first.

    Returns `some proof` of `lhs = rhs` when the AC path applies — i.e. the
    chains' atoms are syntactically identical up to reducible normalization
    (`checkACEligible`) with no loose bvars — using `buildNormProof` for
    O(n log n) kernel work. Returns `none` when the AC path does not apply, so
    the caller can choose a non-AC strategy (pick-based fallback or certificate).
    Throws only on a genuine AC-internal inconsistency (same as the original
    inline code: missing AC instances, or hashes matched but normal forms
    differ). -/
def tryBuildPermProofAC? (lhs rhs : Expr) : MetaM (Option Expr) := do
  -- Try AC fast path with zetaReduce
  let lhsZ ← Lean.Meta.zetaReduce lhs
  let rhsZ ← Lean.Meta.zetaReduce rhs
  -- Not applicable if zetaReduce produced loose bvars
  if lhsZ.hasLooseBVars || rhsZ.hasLooseBVars then return none
  let lhsAtoms ← flattenSepConj lhsZ
  let rhsAtoms ← flattenSepConj rhsZ
  -- Not applicable if atom counts don't match after zetaReduce
  unless lhsAtoms.length == rhsAtoms.length do return none
  -- Trivial cases (0-1 atoms): a defeq check yields refl; otherwise not AC's job
  if lhsAtoms.length ≤ 1 then
    if ← isDefEq lhsZ rhsZ then return some (← mkEqRefl lhsZ)
    else return none
  -- Not applicable if any atom has loose bvars
  if lhsAtoms.any (·.hasLooseBVars) || rhsAtoms.any (·.hasLooseBVars) then return none
  -- Atoms must be syntactically identical (sorted hashes match) for the AC path
  let acEligible ← checkACEligible lhsZ rhsZ
  unless acEligible do return none
  -- AC reflection: normalize each side, check normal forms match
  let op := mkConst ``EvmAsm.Rv64.sepConj
  let some pc ← Lean.Meta.AC.preContext op
    | throwError "xperm: sepConj has no Associative/Commutative instances"
  let some (lHead, lTail) ← parseSepConj? lhsZ
    | throwError "xperm: LHS is not a sepConj chain"
  let some (rHead, rTail) ← parseSepConj? rhsZ
    | throwError "xperm: RHS is not a sepConj chain"
  let (lPf, lNorm) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 1024 }) do
    Lean.Meta.AC.buildNormProof pc lHead lTail
  let (rPf, rNorm) ← withTheReader Core.Context (fun c => { c with maxRecDepth := 1024 }) do
    Lean.Meta.AC.buildNormProof pc rHead rTail
  unless ← isDefEq lNorm rNorm do
    throwError "xperm: AC normal forms differ (atoms matched by hash but not by AC normalization)"
  return some (← mkEqTrans lPf (← mkEqSymm rPf))

/-- The main permutation proof builder.

    Given LHS and RHS as sepConj chains with the same atoms, builds a proof of
    `LHS = RHS`: AC reflection (`tryBuildPermProofAC?`) when atoms are
    syntactically identical, otherwise the pick-based O(n^2) fallback. -/
partial def buildPermProof (lhs rhs : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.perm (fun _ => return m!"perm") do
    match ← tryBuildPermProofAC? lhs rhs with
    | some p => return p
    | none => buildPermProofFallback lhs rhs

/-! ## Certificate permutation prover (re-implementing YOLO's idea)

  This re-implements the *core idea* of YOLO — Valentin Mikhalchuk, Vladimir
  Gladshtein, Ilya Sergey, "Lazy Proof Automation for Separation Logic", ITP 2026
  (to appear); artifact https://github.com/verse-lab/yolo — namely: run the
  (untrusted) atom-matching search *once*, then discharge the whole entailment
  with a *single* cheap verified replay instead of an eager step-by-step proof.
  Credit for that idea belongs to Mikhalchuk, Gladshtein, and Sergey.

  It is an INDEPENDENT re-implementation, NOT a port of YOLO's code: it shares
  none of YOLO's machinery (no `hprop` syntax tree, no left/right worklists, no
  extensible operation-tag typeclasses, no recorded-tactic-script replay). Here
  the search result is recorded as a **data certificate** — an index permutation
  `σ : List Nat` — and the reordering is discharged by one
  `EvmAsm.Rv64.seps_permute_check` whose side condition
  `permCheck σ n = true` (an XOR-clearing bitmask checker equivalent to
  `σ.Perm (List.range n)`, see `perm_range_of_permCheck`) is kernel-checked by
  a single O(n) `decide` with no `isDefEq` on atom expressions.

  This collapses the `O(n²)` proof term / `whnf` count / kernel re-check of
  `buildPermProofFallback` to `O(n)` (the `O(n²)` `isDefEq` *search* is the same
  and irreducible). Always kernel-checked; the certificate `σ` *is* the recorded
  script. Falls back to `buildPermProof` on any unexpected shape. -/

/-- Build a `List Nat` literal from an array of `Nat`s. -/
private def mkNatListExpr (ns : Array Nat) : Expr :=
  let nat := mkConst ``Nat
  ns.foldr (init := mkApp (mkConst ``List.nil [0]) nat)
    fun n acc => mkApp3 (mkConst ``List.cons [0]) nat (mkNatLit n) acc

/-- Find the first still-available LHS atom that is `isDefEq` to `target`.
    Hash pre-filtering (matching-hash bucket first, then reducible `isDefEq`),
    mirroring `findAtomIdx`, but with explicit availability so each atom is
    consumed at most once. -/
private def findAvailIdx (target : Expr) (atoms : Array Expr) (available : Array Bool) :
    MetaM (Option Nat) := do
  let h := target.hash
  for i in [:atoms.size] do
    if available[i]! && atoms[i]!.hash == h then
      if ← isDefEq target atoms[i]! then return some i
  for i in [:atoms.size] do
    if available[i]! && atoms[i]!.hash != h then
      if ← withReducible (isDefEq target atoms[i]!) then return some i
  return none

/-- Compute the index permutation `σ`: for each RHS atom, the original index of
    the matching LHS atom (consuming each LHS atom at most once). -/
private def computeSigma (rhsAtoms lhsAtoms : Array Expr) : MetaM (Array Nat) := do
  let mut available : Array Bool := Array.mk (List.replicate lhsAtoms.size true)
  let mut σ : Array Nat := Array.mkEmpty rhsAtoms.size
  for j in [:rhsAtoms.size] do
    match ← findAvailIdx rhsAtoms[j]! lhsAtoms available with
    | some i =>
      available := available.set! i false
      σ := σ.push i
    | none =>
      throwError "xperm cert: no LHS atom matches RHS atom {j}:\n  {rhsAtoms[j]!}"
  return σ

/-- Certificate proof builder (may throw; callers fall back to `buildPermProof`).
    Returns a proof of `lhs = rhs`. -/
partial def buildPermProofCertCore (lhs rhs : Expr) : MetaM Expr := do
  let lhs ← instantiateMVars lhs
  let rhs ← instantiateMVars rhs
  -- Reassociate to right-associated form so the `seps`-list bridge is `defeq`.
  let (lhsRA, lhsPf) ← reassocProof lhs
  let (rhsRA, rhsPf) ← reassocProof rhs
  let lhsAtoms := (← flattenSepConj lhsRA).toArray
  let rhsAtoms := (← flattenSepConj rhsRA).toArray
  unless lhsAtoms.size == rhsAtoms.size do
    throwError "xperm cert: atom count mismatch ({lhsAtoms.size} vs {rhsAtoms.size})"
  if lhsAtoms.size ≤ 1 then
    throwError "xperm cert: trivial chain, deferring"
  if lhsAtoms.any (·.hasLooseBVars) || rhsAtoms.any (·.hasLooseBVars) then
    throwError "xperm cert: loose bvars in atoms"
  -- YOLO fast phase: search the index permutation once.
  let σ ← computeSigma rhsAtoms lhsAtoms
  -- Single verified certificate: seps lhsList = seps (σ.map (lhsList.getD · emp)).
  -- The side condition is the O(n) `permCheck` Bool checker (n GMP bit ops),
  -- NOT a `decide` on `σ.Perm (List.range n)`: kernel-reducing the `List.Perm`
  -- `Decidable` instance costs ~500ms at 83 atoms and overflows the recursion
  -- depth near 200 atoms (silently dropping to the slow fallback exactly on
  -- the large chains the certificate exists for). Measured ~7ms at n = 83,
  -- ~13ms at n = 200 (see `perm_range_of_permCheck`).
  let lhsList := mkAssertionList lhsAtoms
  let σExpr := mkNatListExpr σ
  let checkProp ← mkEq
    (mkApp2 (mkConst ``EvmAsm.Rv64.permCheck) σExpr (mkNatLit lhsAtoms.size))
    (mkConst ``Bool.true)
  let hσ ← withTheReader Core.Context (fun c => { c with maxRecDepth := 1024 }) do
    mkDecideProof checkProp
  let certPf ← mkAppM ``EvmAsm.Rv64.seps_permute_check #[lhsList, σExpr, hσ]
  -- Emp bridges: lhsRA = empified(lhsRA) (=defeq seps lhsList); same for rhs.
  let (lhsEmpPf, _) ← buildAddEmpProof lhsRA
  let (rhsEmpPf, _) ← buildAddEmpProof rhsRA
  -- lhs =(lhsPf) lhsRA =(lhsEmpPf) seps lhsList =(certPf) seps(σ.map …)
  --     =defeq= seps rhsList =(symm rhsEmpPf) rhsRA =(symm rhsPf) rhs
  let p ← mkEqTrans certPf (← mkEqSymm rhsEmpPf)
  let p ← mkEqTrans lhsEmpPf p
  let p ← mkEqTrans lhsPf p
  let p ← mkEqTrans p (← mkEqSymm rhsPf)
  return p

/-- Drop-in alternative to `buildPermProof` using the certificate prover.
    Wrapped in the `runBlock.perf.perm` trace node; falls back to
    `buildPermProof` on any failure. -/
partial def buildPermProofCert (lhs rhs : Expr) : MetaM Expr :=
  withTraceNode `runBlock.perf.perm (fun _ => return m!"perm-cert") do
    -- Route: certificate → AC reflection → pick-based O(n^2) fallback.
    --
    -- The certificate is tried FIRST. On the real compose proofs it beats even
    -- AC reflection: the AC gate (`checkACEligible`'s per-atom
    -- `normalizeAtomForHash`, a full reducible-whnf tree transform) plus
    -- `buildNormProof` costs *more* than computing the index permutation once +
    -- one `seps_permute` + `decide`. Measured on DivMod/LoopComposeN3:
    -- cert-first ~2.15s vs AC-first ~2.70s vs baseline 2.69s — trying AC first
    -- pays the AC-gate cost and throws away the win.
    --
    -- AC reflection is kept only as a safety net (for any shape the certificate
    -- can't handle but AC can), ahead of the O(n^2) pick-based fallback.
    try
      buildPermProofCertCore lhs rhs
    catch e =>
      trace[runBlock.perf.perm] "xperm cert-core fallback: {e.toMessageData}"
      match ← tryBuildPermProofAC? lhs rhs with
      | some p => return p
      | none => buildPermProofFallback lhs rhs

/-- Dispatch between the baseline and certificate permutation provers based on
    the `xperm.cert` option (default `false` ⇒ baseline `buildPermProof`). All
    `xperm`-family entry points route through this. -/
def buildPermProofDispatch (lhs rhs : Expr) : MetaM Expr := do
  if xperm.cert.get (← getOptions) then buildPermProofCert lhs rhs
  else buildPermProof lhs rhs

/-- `xperm` tactic: proves `⊢ P = Q` where P and Q are AC-permutations of
    sepConj chains, using `isDefEq` for atom matching. -/
elab "xperm" : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let some (_, lhsExpr, rhsExpr) := Expr.eq? goalType
    | throwError "xperm: goal is not an equality, got:\n{goalType}"
  let proof ← buildPermProofDispatch lhsExpr rhsExpr
  goal.assign proof

end EvmAsm.Rv64.Tactics
