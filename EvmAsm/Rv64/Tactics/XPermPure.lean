/-
# `xperm_pure` — slice 2 of #1435 (beads evm-asm-8py)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

`xperm_pure h` is a sibling of `xperm_hyp` that tolerates pure (`⌜·⌝`)
atoms in the source hypothesis and/or the goal. It composes the
`extract_pure` machinery (#1432, `EvmAsm/Rv64/Tactics/ExtractPure.lean`)
with `xperm_hyp` (`EvmAsm/Rv64/Tactics/XSimp.lean`).

## Semantics

Given a hypothesis `h : H s` and goal `⊢ G s` where each of `H` and `G`
is an AC-tree of `**` whose resource leaves match (up to AC) and whose
pure leaves on the goal side are derivable from the pure leaves on the
hypothesis side, `xperm_pure h` closes the goal.

Concretely, `xperm_pure h`:

1. Runs `extract_pure` on the hypothesis, peeling every `⌜P_i⌝` atom
   into a `∧`-chain. After this `h : P₁ ∧ … ∧ Pₖ ∧ Hr s` where `Hr`
   is the resource-only tail.
2. Runs the same `simp only` lemma set on the goal, peeling every
   goal-side `⌜Q_j⌝` atom analogously. After this the goal is
   `Q₁ ∧ … ∧ Qₘ ∧ Gr s`.
3. Decomposes the hypothesis pure conjuncts into the local context.
4. Splits the goal `And`s, discharging each pure side with
   `assumption` / `decide`, leaving the resource side.
5. Closes the resource side with `xperm_hyp h`.

For the common case where neither side has any pure atoms (Flavor C
in the slice-1 design note), `xperm_pure h` degrades cleanly to
`xperm_hyp h`.
-/

import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic

/-- Run a tactic on every currently-open goal, in order. Equivalent
    to Mathlib's `Lean.Elab.Tactic.allGoals` but inlined here to keep
    `XPermPure.lean` Mathlib-free. -/
private def runOnAllGoals (tac : TacticM Unit) : TacticM Unit := do
  let mvarIds ← getGoals
  let mut newGoals := #[]
  for mvarId in mvarIds do
    unless ← mvarId.isAssigned do
      setGoals [mvarId]
      tac
      newGoals := newGoals ++ (← getUnsolvedGoals)
  setGoals newGoals.toList

/-- Repeatedly split the leading `∧` in the main goal into two
    focused sub-goals, recursing into both branches. After this runs
    every leaf in the conjunction tree becomes an open goal — the
    resource leaf and any leftover pure leaves. -/
partial def xpermPureSplitGoal : TacticM Unit := do
  let goalType ← instantiateMVars (← (← getMainGoal).getType)
  if goalType.isAppOfArity ``And 2 then
    evalTactic (← `(tactic| refine ⟨?_, ?_⟩))
    runOnAllGoals xpermPureSplitGoal
  else
    return

/-- Repeatedly destructure the leading `∧` in `h`'s type, naming the
    head conjunct under a fresh ident (so `assumption` finds it
    later) and rebinding `h` to the tail. -/
partial def xpermPureDestructHyp (h : TSyntax `ident) : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let some hDecl := lctx.findFromUserName? h.getId | return
    let ty ← instantiateMVars hDecl.type
    if ty.isAppOfArity ``And 2 then
      let fresh ← Lean.Elab.Term.mkFreshIdent (Lean.mkIdent `pureAtom)
      evalTactic (← `(tactic| obtain ⟨$fresh:ident, $h:ident⟩ := $h:ident))
      xpermPureDestructHyp h
    else
      return

/-- Pure-aware variant of `xperm_hyp`. See file docstring. -/
syntax (name := xpermPure) "xperm_pure " ident : tactic

@[tactic xpermPure]
def evalXpermPure : Tactic := fun stx => do
  match stx with
  | `(tactic| xperm_pure $h:ident) => withMainContext do
      -- Step 1: peel pures from the hypothesis. Use `try` so that a
      -- bare resource hypothesis (no pures, no `**`) is left
      -- untouched.
      evalTactic (← `(tactic| try extract_pure $h:ident))
      -- Step 2: peel pures from the goal via the same simp lemma set.
      evalTactic (← `(tactic|
        try
          simp only
            [ ← EvmAsm.Rv64.sepConj_assoc'
            , EvmAsm.Rv64.sepConj_pure_right
            , EvmAsm.Rv64.sepConj_pure_left
            , EvmAsm.Rv64.Tactics.sepConj_pure_mid_left
            , EvmAsm.Rv64.Tactics.sepConj_pure_mid_right
            , EvmAsm.Rv64.sepConj_emp_left'
            , EvmAsm.Rv64.sepConj_emp_right'
            ]))
      -- Step 3: destructure hypothesis pure conjuncts under fresh
      -- names so step 4's `assumption` can reach them.
      xpermPureDestructHyp h
      -- Step 4: split goal `And`s; each leaf becomes a focused goal.
      xpermPureSplitGoal
      -- Step 5: close every leaf. The resource leaf closes via
      -- `xperm_hyp h`; the pure leaves close via `assumption` /
      -- `decide`. `first` picks the right tactic per goal.
      runOnAllGoals do
        evalTactic (← `(tactic| first
          | xperm_hyp $h:ident
          | assumption
          | decide))
  | _ => throwUnsupportedSyntax

end EvmAsm.Rv64.Tactics

/- ============================================================================
   Smoke tests
   ============================================================================
   These mirror the shapes that motivated #1435: pure atoms on the
   hypothesis side, on the goal side, on both sides, and asymmetric
   between the two. They use only the separation-logic vocabulary
   from `Rv64/SepLogic.lean` and don't depend on any RISC-V program /
   spec infrastructure. -/

namespace EvmAsm.Rv64.Tactics.XPermPureTests

open EvmAsm.Rv64

/-- Flavor A: pure on hypothesis, none on goal. -/
example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** R₂ ** ⌜P⌝) s) : (R₂ ** R₁) s := by
  xperm_pure h

/-- Flavor B: pure on both sides, asymmetric position. -/
example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** R₂ ** ⌜P⌝) s) : (⌜P⌝ ** R₂ ** R₁) s := by
  xperm_pure h

/-- Goal pure derivable by `decide`. -/
example (s : PartialState) (R : Assertion)
    (h : R s) : (R ** ⌜(1 : Nat) + 1 = 2⌝) s := by
  xperm_pure h

/-- No pure atoms on either side: must degrade to `xperm_hyp`. -/
example (s : PartialState) (R₁ R₂ R₃ : Assertion)
    (h : (R₁ ** R₂ ** R₃) s) : (R₃ ** R₁ ** R₂) s := by
  xperm_pure h

/-- Multiple pures on the hypothesis, single pure on the goal,
    derivable via `assumption` from one of the destructured pures. -/
example (s : PartialState) (P Q : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂ ** ⌜Q⌝) s) : (R₂ ** R₁ ** ⌜P⌝) s := by
  xperm_pure h

end EvmAsm.Rv64.Tactics.XPermPureTests
