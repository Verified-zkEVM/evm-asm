/-
  EvmAsm.Rv32.Tactics.XCancel

  Separation logic cancellation tactic, built on the XPerm infrastructure.

  ## Usage

  ```
  -- Given hypothesis h : (A ** B ** C ** D) s and goal (A ** C ** ?Frame) s:
  xcancel h
  -- Closes the goal, unifying ?Frame with (B ** D)
  ```

  ## Algorithm

  Given `h : (P₁ ** P₂ ** ... ** Pₙ) s` and goal `(Q₁ ** ... ** Qₘ ** ?F) s`:
  1. Flatten both sides to atom lists
  2. Match each concrete Qⱼ against some Pᵢ (using `isDefEq`), consuming it
  3. Compute the frame as unmatched P atoms
  4. Unify ?F with the frame
  5. Close the goal via a permutation proof
-/

import Lean
import EvmAsm.Rv32.Tactics.XPerm

open Lean Meta Elab Tactic

namespace EvmAsm.Tactics

/-- Build a right-associated sepConj chain from a list of atoms.
    Empty list → `empAssertion`, singleton → the atom, otherwise fold right. -/
def buildSepConjChain : List Expr → MetaM Expr
  | [] => return mkConst ``EvmAsm.empAssertion
  | [a] => return a
  | a :: rest => do
    let tail ← buildSepConjChain rest
    return mkApp2 (mkConst ``EvmAsm.sepConj) a tail

/-- Match goal atoms against hypothesis atoms using `isDefEq`.
    Each goal atom is either matched against a hyp atom (consuming it) or
    identified as the frame metavariable.
    Returns `(consumedHypIndices, frameMVar?)`. -/
private def matchGoalAgainstHyp (hypAtoms goalAtoms : Array Expr) :
    MetaM (Array Nat × Option Expr) := do
  -- Track which hyp atoms are still available: `available[i] = true` means not yet matched
  let mut available := (Array.mk (List.replicate hypAtoms.size true) : Array Bool)
  let mut matched : Array Nat := #[]
  let mut frameMVar : Option Expr := none
  for goalAtom in goalAtoms do
    let ga ← instantiateMVars goalAtom
    if ga.isMVar then
      frameMVar := some ga
    else
      let mut found := false
      for i in [:hypAtoms.size] do
        if available[i]! then
          if ← withReducible (isDefEq goalAtom hypAtoms[i]!) then
            available := available.set! i false
            matched := matched.push i
            found := true
            break
      unless found do
        throwError "xcancel: no hypothesis atom matches goal atom:\n  {goalAtom}"
  return (matched, frameMVar)

/-- Collect unmatched hyp atoms (those not consumed by goal matching). -/
private def unmatchedAtoms (hypAtoms : Array Expr) (matchedIndices : Array Nat) : List Expr :=
  let matchedSet := matchedIndices.toList
  hypAtoms.toList.zipIdx.filterMap fun (atom, i) =>
    if matchedSet.contains i then none else some atom

/-- `xcancel hyp` closes a goal `Q s` given `hyp : P s` where Q may contain
    a metavariable (frame). Matches Q's concrete atoms against P's atoms,
    sets the frame to the residual, and closes the goal via a permutation proof. -/
elab "xcancel" hyp:ident : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let hypExpr ← elabTerm hyp none
  let hypType ← inferType hypExpr

  let hypAssertion := Expr.appFn! hypType
  let goalAssertion := Expr.appFn! goalType
  let stateExpr := Expr.appArg! hypType

  let hypAtoms := (← flattenSepConj hypAssertion).toArray
  let goalAtoms := (← flattenSepConj goalAssertion).toArray

  -- Match goal atoms against hyp atoms
  let (matchedIndices, frameMVar?) ← matchGoalAgainstHyp hypAtoms goalAtoms

  -- Compute unmatched (residual) atoms
  let residual := unmatchedAtoms hypAtoms matchedIndices

  -- Build frame and unify with metavar if present
  let frameExpr ← buildSepConjChain residual
  match frameMVar? with
  | some mv =>
    unless ← isDefEq mv frameExpr do
      throwError "xcancel: failed to unify frame metavar with:\n  {frameExpr}"
  | none =>
    unless residual.isEmpty do
      throwError "xcancel: no frame metavar but {residual.length} atoms unmatched"

  -- Build permutation proof: hypAssertion = goalAssertionInst
  let goalAssertionInst ← instantiateMVars goalAssertion
  let permProof ← buildPermProof hypAssertion goalAssertionInst
  -- Close goal: Eq.mp (congrFun permProof s) hyp
  let proof ← mkEqMP (← mkCongrFun permProof stateExpr) hypExpr
  goal.assign proof

end EvmAsm.Tactics
