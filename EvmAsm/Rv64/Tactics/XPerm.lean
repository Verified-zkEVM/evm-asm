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
import EvmAsm.Rv64.SepLogic

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
  for i in [:atoms.size] do
    if atoms[i]!.hash != h then
      if ← isDefEq target atoms[i]! then return some i
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

/-- The main permutation proof builder.

    Given LHS and RHS as sepConj chains with the same atoms
    (up to `isDefEq`), builds a proof of `LHS = RHS`.
    Handles non-right-associated chains by first reassociating.

    **Optimization**: flattens LHS once and passes the atom array through
    recursion (avoiding O(n²) re-flattening). -/
partial def buildPermProof (lhs rhs : Expr) : MetaM Expr := do
  -- First reassociate both sides to right-associated form
  let (lhsRA, lhsPf) ← reassocProof lhs
  let (rhsRA, rhsPf) ← reassocProof rhs
  -- Flatten LHS once (not per-atom)
  let lhsAtoms := (← flattenSepConj lhsRA).toArray
  let rhsAtoms := (← flattenSepConj rhsRA).toArray
  -- Build permutation proof on right-associated forms
  let permPf ← buildPermProofAux lhsRA lhsAtoms rhsAtoms
  -- Chain: lhs = lhsRA = rhsRA = rhs
  let step1 ← mkEqTrans lhsPf permPf
  let rhsPfSymm ← mkEqSymm rhsPf
  mkEqTrans step1 rhsPfSymm
where
  /-- Inner loop: pick each RHS atom from the LHS chain.
      `lhsAtoms` is the cached atom array (updated by erasing matched elements). -/
  buildPermProofAux (currentLhs : Expr) (lhsAtoms : Array Expr)
      (remainingRhs : Array Expr) (startIdx : Nat := 0) : MetaM Expr := do
    if startIdx >= remainingRhs.size then
      mkEqRefl currentLhs
    else if startIdx + 1 == remainingRhs.size then
      -- Last atom: they should be isDefEq
      let target := remainingRhs[startIdx]!
      if lhsAtoms.size == 1 then
        if ← isDefEq currentLhs target then
          mkEqRefl currentLhs
        else
          throwError "xperm: final atoms don't match:\n  LHS: {currentLhs}\n  RHS: {target}"
      else
        throwError "xperm: LHS has {lhsAtoms.size} atoms but only 1 remaining in RHS"
    else
      -- Early termination: if remaining LHS atoms already match RHS in order, short-circuit.
      -- This avoids O(m²) picks when only a few atoms were rearranged (common in seqFrame).
      if lhsAtoms.size == remainingRhs.size - startIdx then
        let mut hashesMatch := true
        for j in [:lhsAtoms.size] do
          if lhsAtoms[j]!.hash != remainingRhs[startIdx + j]!.hash then
            hashesMatch := false
            break
        if hashesMatch then
          -- Hashes match — build remaining RHS chain and verify with isDefEq
          let endIdx := remainingRhs.size
          let mut rhsChain := remainingRhs[endIdx - 1]!
          for j' in [:endIdx - startIdx - 1] do
            let j := endIdx - 2 - j'
            rhsChain := mkApp2 (mkConst ``EvmAsm.Rv64.sepConj) remainingRhs[j]! rhsChain
          if ← withoutModifyingState (isDefEq currentLhs rhsChain) then
            return ← mkEqRefl currentLhs
      let target := remainingRhs[startIdx]!
      -- Find target in cached LHS atoms (no re-flattening)
      let some idx ← findAtomIdx target lhsAtoms
        | throwError "xperm: could not find atom in LHS matching RHS atom:\n  target: {target}\n  LHS ({lhsAtoms.size} atoms)"
      -- Build pick proof: currentLhs = pickedRhs (returns RHS directly, no inferType needed)
      let (pickProof, pickedRhs) ← buildPickProof currentLhs idx
      match ← parseSepConj? pickedRhs with
      | none =>
        throwError "xperm: picked result is a single atom but {remainingRhs.size - startIdx} RHS atoms remain"
      | some (pickedHead, pickedTail) =>
        -- Update cached atoms: remove the matched element
        let newLhsAtoms := arrayEraseIdx lhsAtoms idx
        if startIdx + 2 == remainingRhs.size then
          -- Exactly 2 remaining: pickedTail should match the last RHS atom
          let lastTarget := remainingRhs[startIdx + 1]!
          if ← isDefEq pickedTail lastTarget then
            let tailProof ← mkEqRefl pickedTail
            let sepConjPicked := mkApp (mkConst ``EvmAsm.Rv64.sepConj) pickedHead
            let step2 ← mkCongrArg sepConjPicked tailProof
            mkEqTrans pickProof step2
          else
            throwError "xperm: last two atoms don't match:\n  LHS tail: {pickedTail}\n  RHS last: {lastTarget}"
        else
          -- Recursively process the tail with updated atom cache
          let tailProof ← buildPermProofAux pickedTail newLhsAtoms remainingRhs (startIdx + 1)
          let sepConjPicked := mkApp (mkConst ``EvmAsm.Rv64.sepConj) pickedHead
          let step2 ← mkCongrArg sepConjPicked tailProof
          mkEqTrans pickProof step2

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
