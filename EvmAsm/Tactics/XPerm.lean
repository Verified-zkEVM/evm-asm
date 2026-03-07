/-
  EvmAsm.Tactics.XPerm

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
import EvmAsm.SepLogic

open Lean Meta Elab Tactic

namespace EvmAsm.Tactics

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
  if Expr.isAppOfArity e ``EvmAsm.sepConj 2 then
    return some (Expr.appArg! (Expr.appFn! e), Expr.appArg! e)
  return none

/-- Flatten a right-associated sepConj chain into a list of atoms.
    `A ** (B ** (C ** D))` becomes `[A, B, C, D]`. -/
partial def flattenSepConj (e : Expr) : MetaM (List Expr) := do
  match ← parseSepConj? e with
  | some (l, r) => return l :: (← flattenSepConj r)
  | none => return [e]

/-- Find the index of an atom in an array that is `isDefEq` to the target. -/
def findAtomIdx (target : Expr) (atoms : Array Expr) : MetaM (Option Nat) := do
  for i in [:atoms.size] do
    if ← isDefEq target atoms[i]! then
      return some i
  return none

/-- Build a proof that picks the element at index `k` to the front of a
    right-associated sepConj chain.

    Given chain = A₀ ** (A₁ ** (... ** (Aₖ ** ...))),
    returns a proof of:
      chain = Aₖ ** (A₀ ** (A₁ ** (...)))
-/
partial def buildPickProof (chain : Expr) (k : Nat) : MetaM Expr := do
  if k == 0 then
    mkEqRefl chain
  else
    -- Normalize chain to expose sepConj structure
    let chainN ← normForSepConj chain
    match ← parseSepConj? chainN with
    | none => throwError "buildPickProof: expected sepConj at index {k}, got:\n{chainN}"
    | some (head, tail) =>
      -- If chain was normalized, we need to account for the definitional equality
      -- chain =def= chainN = head ** tail
      -- We'll work with chainN and rely on definitional equality
      let innerProof ← buildPickProof tail (k - 1)
      -- innerProof : tail = innerRHS
      let sepConjHead := mkApp (mkConst ``EvmAsm.sepConj) head
      let step1 ← mkCongrArg sepConjHead innerProof
      -- step1 : head ** tail = head ** innerRHS
      let innerType ← inferType innerProof
      let some (_, _, innerRHS) := Expr.eq? innerType
        | throwError "buildPickProof: inner proof is not an equality"
      match ← parseSepConj? innerRHS with
      | none =>
        -- Two-element case: head ** target → target ** head
        let step2 := mkApp2 (mkConst ``EvmAsm.sepConj_comm') head innerRHS
        mkEqTrans step1 step2
      | some (target, rest) =>
        -- Three+ element case: head ** (target ** rest) → target ** (head ** rest)
        let step2 := mkApp3 (mkConst ``EvmAsm.sepConj_left_comm') head target rest
        mkEqTrans step1 step2

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
      let newE := mkApp2 (mkConst ``EvmAsm.sepConj) l r'
      let pf ← mkCongrArg (mkApp (mkConst ``EvmAsm.sepConj) l) rPf
      return (newE, pf)
    | some (ll, lr) =>
      -- e =def= (ll ** lr) ** r → need to assoc to ll ** (lr ** r), then recurse
      let assocPf := mkApp3 (mkConst ``EvmAsm.sepConj_assoc') ll lr r
      -- assocPf : (ll ** lr) ** r = ll ** (lr ** r)
      let newInner := mkApp2 (mkConst ``EvmAsm.sepConj) lr r
      let newE := mkApp2 (mkConst ``EvmAsm.sepConj) ll newInner
      -- Recurse (the new expression might still need reassociation)
      let (result, restPf) ← reassocProof newE
      let pf ← mkEqTrans assocPf restPf
      return (result, pf)

/-- The main permutation proof builder.

    Given LHS and RHS as sepConj chains with the same atoms
    (up to `isDefEq`), builds a proof of `LHS = RHS`.
    Handles non-right-associated chains by first reassociating. -/
partial def buildPermProof (lhs rhs : Expr) : MetaM Expr := do
  -- First reassociate both sides to right-associated form
  let (lhsRA, lhsPf) ← reassocProof lhs
  let (rhsRA, rhsPf) ← reassocProof rhs
  -- Build permutation proof on right-associated forms
  let rhsAtoms ← flattenSepConj rhsRA
  let permPf ← buildPermProofAux lhsRA rhsAtoms.toArray
  -- Chain: lhs = lhsRA = rhsRA = rhs
  let step1 ← mkEqTrans lhsPf permPf
  let rhsPfSymm ← mkEqSymm rhsPf
  mkEqTrans step1 rhsPfSymm
where
  buildPermProofAux (currentLhs : Expr) (remainingRhs : Array Expr) (startIdx : Nat := 0) :
      MetaM Expr := do
    if startIdx >= remainingRhs.size then
      mkEqRefl currentLhs
    else if startIdx + 1 == remainingRhs.size then
      -- Last atom: they should be isDefEq
      let target := remainingRhs[startIdx]!
      let currentAtoms ← flattenSepConj currentLhs
      if currentAtoms.length == 1 then
        if ← isDefEq currentLhs target then
          mkEqRefl currentLhs
        else
          throwError "xperm: final atoms don't match:\n  LHS: {currentLhs}\n  RHS: {target}"
      else
        throwError "xperm: LHS has {currentAtoms.length} atoms but only 1 remaining in RHS"
    else
      let target := remainingRhs[startIdx]!
      let currentAtoms := (← flattenSepConj currentLhs).toArray
      -- Find target in current LHS atoms
      let some idx ← findAtomIdx target currentAtoms
        | throwError "xperm: could not find atom in LHS matching RHS atom:\n  target: {target}\n  LHS ({currentAtoms.size} atoms)"
      -- Build pick proof: currentLhs = pickedRhs
      let pickProof ← buildPickProof currentLhs idx
      -- Get the "pickedRhs" after picking
      let pickType ← inferType pickProof
      let some (_, _, pickedRhs) := Expr.eq? pickType
        | throwError "xperm: pick proof is not an equality"
      match ← parseSepConj? pickedRhs with
      | none =>
        throwError "xperm: picked result is a single atom but {remainingRhs.size - startIdx} RHS atoms remain"
      | some (pickedHead, pickedTail) =>
        if startIdx + 2 == remainingRhs.size then
          -- Exactly 2 remaining: pickedTail should match the last RHS atom
          let lastTarget := remainingRhs[startIdx + 1]!
          if ← isDefEq pickedTail lastTarget then
            let tailProof ← mkEqRefl pickedTail
            let sepConjPicked := mkApp (mkConst ``EvmAsm.sepConj) pickedHead
            let step2 ← mkCongrArg sepConjPicked tailProof
            mkEqTrans pickProof step2
          else
            throwError "xperm: last two atoms don't match:\n  LHS tail: {pickedTail}\n  RHS last: {lastTarget}"
        else
          -- Recursively process the tail
          let tailProof ← buildPermProofAux pickedTail remainingRhs (startIdx + 1)
          let sepConjPicked := mkApp (mkConst ``EvmAsm.sepConj) pickedHead
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

end EvmAsm.Tactics
