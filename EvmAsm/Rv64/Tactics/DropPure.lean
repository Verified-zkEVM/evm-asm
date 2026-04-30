/-
# `drop_pure` — slice of #1435 (beads evm-asm-ww8)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

`drop_pure h` is a sibling of `extract_pure` (#1432,
`EvmAsm/Rv64/Tactics/ExtractPure.lean`) that strips every `⌜P⌝` leaf from
`h`'s separation-conjunction chain and rebinds `h` to the bare resource
tail — *not* to an `And`-chain.

## Why a separate tactic

`extract_pure h` rewrites `h : (… ** ⌜P⌝ ** … ** ⌜Q⌝ ** R) s` into the
∧-chain `P ∧ Q ∧ R s`. That shape is convenient when the caller wants
to consume the pures (the canonical pattern is
`extract_pure h; obtain ⟨hP, hQ, h⟩ := h`).

But for the Flavor-A friction noted in beads `evm-asm-kvl` —
*hypothesis* has a pure mid-chain, *goal* has no pure — what the caller
really wants is just the resource tail in `h`'s slot, with the pures
discarded so a follow-up `xperm_hyp h` works directly with no
destructuring and no `Eq.mp`/`congrFun` reflection mismatches from
half-extracted shapes.

`xperm_pure h` (#1435 slice 2) handles the symmetric case where both
sides may carry pures and the goal needs `xperm_hyp` after pure
splitting; it does the destructure-and-split internally. `drop_pure h`
is the thinner sibling: it does *only* the rebind, leaving the user
free to pick whatever follow-up tactic fits (`xperm_hyp`, `xcancel`,
direct `exact`, …).

## Behaviour

Given `h : (A₁ ** … ** Aₙ) s` (with zero or more `Aᵢ = ⌜Pᵢ⌝`):

1. AC-normalise the chain via `extract_pure`'s simp lemma set so every
   pure leaf bubbles into a left `∧`.
2. Repeatedly project `.2` off `h`'s leading `∧` until the type is no
   longer of the form `_ ∧ _`. The pure conjuncts are discarded
   (no fresh names introduced).

Result: `h : (B₁ ** … ** Bₘ) s` where `Bⱼ` are the resource leaves of
the original chain, in `extract_pure`'s canonical AC-normal order.

If the original chain has no pure leaves, the simp step is a no-op and
the `.2` loop exits immediately, leaving `h` untouched.

## Smoke tests

The tests at the bottom of this file mirror the shapes that motivated
the kvl friction note: a single pure mid-chain, multiple pures, and the
no-pure case. They share infrastructure with `ExtractPure`'s and
`XPermPure`'s smoke tests but assert the post-tactic *type* of `h` is
the bare resource chain, not an `And`.
-/

import EvmAsm.Rv64.Tactics.ExtractPure
import EvmAsm.Rv64.Tactics.XSimp

namespace EvmAsm.Rv64.Tactics

open Lean Elab Tactic Meta

/-- Variant of `sepConj_pure_right` that places the pure atom on the
    *left* of the resulting `And`, matching the convention used by
    `sepConj_pure_left`, `sepConj_pure_mid_left`, and
    `sepConj_pure_mid_right`. We need this for `drop_pure` so the
    pure-shedding loop can uniformly project `.2`. -/
theorem sepConj_pure_right_swap {P : EvmAsm.Rv64.Assertion} {Q : Prop} :
    ∀ s, (P ** ⌜Q⌝) s ↔ Q ∧ P s := by
  intro s
  rw [EvmAsm.Rv64.sepConj_pure_right]
  exact And.comm

/-- Repeatedly project off the leading `And` in `h`'s type, discarding
    the head conjunct and rebinding `h` to the tail. Stops as soon as
    the type is no longer of the form `_ ∧ _`. -/
partial def dropPureLoop (h : TSyntax `ident) : TacticM Unit :=
  withMainContext do
    let lctx ← getLCtx
    let some hDecl := lctx.findFromUserName? h.getId | return
    let ty ← instantiateMVars hDecl.type
    if ty.isAppOfArity ``And 2 then
      evalTactic (← `(tactic| replace $h:ident := $h:ident |>.2))
      dropPureLoop h
    else
      return

/-- Walk the right-associated `**` chain rooted at `e` (an `Assertion`)
    and split its leaves into (pure-leaves, resource-leaves). A leaf is
    a `**`-free subterm; a pure leaf is one of the form `⌜P⌝`
    (i.e. `EvmAsm.Rv64.pure P`).

    `**` is right-associative, but we tolerate left-nests by recursing
    on both sides. Order is preserved within each list so the rebuilt
    chain matches the user's reading order. -/
private partial def collectSepLeaves
    (e : Expr) : MetaM (Array Expr × Array Expr) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``EvmAsm.Rv64.sepConj, #[l, r]) =>
      let (lp, lr) ← collectSepLeaves l
      let (rp, rr) ← collectSepLeaves r
      return (lp ++ rp, lr ++ rr)
  | _ =>
      match e.getAppFnArgs with
      | (``EvmAsm.Rv64.pure, _) => return (#[e], #[])
      | _                       => return (#[], #[e])

/-- Right-fold an array of `Assertion` expressions into a `**`-chain.
    `[A]` ↦ `A`. `[A, B, C]` ↦ `A ** B ** C` (right-assoc). Empty
    array becomes `empAssertion`. -/
private def buildSepChain (xs : Array Expr) : MetaM Expr := do
  if xs.isEmpty then
    return mkConst ``EvmAsm.Rv64.empAssertion
  let n := xs.size
  let mut acc := xs[n - 1]!
  for i in [0:n - 1] do
    let j := n - 2 - i
    acc ← mkAppM ``EvmAsm.Rv64.sepConj #[xs[j]!, acc]
  return acc

/-- `drop_pure h` strips every `⌜P⌝` leaf from the `**`-chain in `h`'s
    type and rebinds `h` to the bare resource tail.

    Implementation (beads `evm-asm-22a`): we walk `h`'s assertion
    expression, partition its leaves into pure (`⌜·⌝`) vs resource,
    rebuild the chain with all pure atoms moved to the left, prove the
    rearrangement equality with `ac_rfl` (which uses the
    `Std.Associative`/`Std.Commutative` instances on `**`), rewrite
    `h` through it, then peel pures via `sepConj_pure_left` /
    `sepConj_pure_right_swap` and `.2`-projection.

    Older versions of this tactic used a simp set of `↔`-style
    bubble lemmas; those only fired at the outermost state-applied
    position and so left pures untouched at depth ≥ 2 in long chains
    (e.g. 10-atom hypotheses with the pure at depth 8). The
    `ac_rfl`-based approach is depth-agnostic.

    Example:
    ```
    example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
        (h : (R₁ ** ⌜P⌝ ** R₂) s) : (R₂ ** R₁) s := by
      drop_pure h
      xperm_hyp h
    ```

    See file docstring for the full behaviour and the design rationale. -/
syntax (name := dropPure) "drop_pure " ident : tactic

@[tactic dropPure]
def evalDropPure : Tactic := fun stx => do
  match stx with
  | `(tactic| drop_pure $h:ident) => withMainContext do
      -- Step 1: inspect h's type. Expect `(<chain>) s` for some
      -- assertion chain. If it's not of that shape (or has no pures),
      -- fall through to the `.2` peeling loop, which is a no-op on
      -- non-`And` types.
      let lctx ← getLCtx
      let some hDecl := lctx.findFromUserName? h.getId | return
      let hTy ← instantiateMVars hDecl.type
      -- hTy has shape `assertion s`. Get the assertion expr.
      let assertionExpr ← do
        match hTy with
        | .app a _ => Pure.pure a
        | _        => return  -- not in the expected shape; bail.
      let (pures, resources) ← collectSepLeaves assertionExpr
      if pures.isEmpty then
        -- Nothing to strip. Drop through to the .2 loop in case the
        -- caller passed an already-`And` hypothesis.
        dropPureLoop h
        return
      -- Step 2: build the rearranged chain `⌜P₁⌝ ** … ** ⌜Pₖ⌝ ** R₁ ** … ** Rₘ`.
      -- If there are no resources, fall back to `empAssertion` on the
      -- right (the `_emp_left'` rewrite in step 4 cleans it up).
      let resourceChain ← buildSepChain resources
      let allLeaves := pures ++ #[resourceChain]
      let target ← buildSepChain allLeaves
      -- Step 3: rewrite `h` through the AC equality. We construct the
      -- equality term `assertionExpr = target` and prove it with
      -- `ac_rfl` (which uses the registered `Std.Associative` /
      -- `Std.Commutative` instances on `**`), then `rw` it into `h`.
      let eqTy ← Meta.mkEq assertionExpr target
      let lhsStx ← Lean.PrettyPrinter.delab assertionExpr
      let rhsStx ← Lean.PrettyPrinter.delab target
      let _ := eqTy
      evalTactic (← `(tactic| (
        have h_ac_rearrange : $lhsStx = $rhsStx := by ac_rfl
        rw [h_ac_rearrange] at $h:ident
        clear h_ac_rearrange)))
      -- Step 4: peel pures off the left via simp (lifts `⌜P⌝ ** …` to
      -- `P ∧ …` at the outermost s-position). For a single trailing
      -- pure (rare, but possible if resources is empty after rearrange)
      -- `sepConj_pure_right_swap` handles the closing case. The
      -- `_emp_*'` rewrites tidy up the empty-resource degenerate.
      evalTactic (← `(tactic|
        simp only
          [ EvmAsm.Rv64.sepConj_pure_left
          , EvmAsm.Rv64.Tactics.sepConj_pure_right_swap
          , EvmAsm.Rv64.sepConj_emp_left'
          , EvmAsm.Rv64.sepConj_emp_right'
          ] at $h:ident))
      -- Step 5: peel `And`s off the front of `h` until none remain.
      dropPureLoop h
  | _ => throwUnsupportedSyntax

end EvmAsm.Rv64.Tactics

/- ============================================================================
   Smoke tests
   ============================================================================
   Each test asserts that after `drop_pure h`, `h`'s type is the bare
   resource chain by closing the goal with a single `xperm_hyp h` /
   `exact h`. If `drop_pure` left an `And` on `h` either tactic would
   fail, so a green build proves the rebind shape.
-/

namespace EvmAsm.Rv64.Tactics.DropPureTests

open EvmAsm.Rv64

/-- Single pure on the right of a resource. After `drop_pure` the bare
    resource matches the goal directly. -/
example (s : PartialState) (P : Prop) (R : Assertion)
    (h : (R ** ⌜P⌝) s) : R s := by
  drop_pure h
  exact h

/-- Single pure on the left. -/
example (s : PartialState) (P : Prop) (R : Assertion)
    (h : (⌜P⌝ ** R) s) : R s := by
  drop_pure h
  exact h

/-- Pure mid-chain — the kvl Flavor-A friction shape. -/
example (s : PartialState) (P : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂) s) : (R₂ ** R₁) s := by
  drop_pure h
  xperm_hyp h

/-- Multiple pures spread across a resource chain. -/
example (s : PartialState) (P Q : Prop) (R₁ R₂ : Assertion)
    (h : (R₁ ** ⌜P⌝ ** R₂ ** ⌜Q⌝) s) : (R₂ ** R₁) s := by
  drop_pure h
  xperm_hyp h

/-- Three pures, one resource leaf. -/
example (s : PartialState) (P Q R : Prop) (A : Assertion)
    (h : (⌜P⌝ ** A ** ⌜Q⌝ ** ⌜R⌝) s) : A s := by
  drop_pure h
  exact h

/-- Degenerate: no pures. `drop_pure` should be a no-op. -/
example (s : PartialState) (R₁ R₂ R₃ : Assertion)
    (h : (R₁ ** R₂ ** R₃) s) : (R₃ ** R₁ ** R₂) s := by
  drop_pure h
  xperm_hyp h

/- Long-chain regression tests for beads `evm-asm-22a` / GH #1435.

The original DropPure simp set (built on `← sepConj_assoc'` plus the
`∀ s, … ↔ …`-style mid lemmas) only stripped pures at depth ≤ 1 in a
right-associated chain. The reproducer surfaced in beads `evm-asm-ui7`
(Div128Step1v2.lean) where a 10-atom hypothesis with `⌜rhatHi2 ≠ 0⌝` at
depth 9 caused `xperm_hyp` to fail with "LHS has 2 atoms but only 1
remaining in RHS". The cases below lock the contract for chains of
length 8–10 with the pure at varying depths. -/

/-- 8-atom chain, pure at depth 4. -/
example (s : PartialState) (P : Prop) (R₁ R₂ R₃ R₄ R₅ R₆ R₇ : Assertion)
    (h : (R₁ ** R₂ ** R₃ ** R₄ ** ⌜P⌝ ** R₅ ** R₆ ** R₇) s) :
    (R₇ ** R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆) s := by
  drop_pure h
  xperm_hyp h

/-- 10-atom chain, pure at depth 8 (the kvl Flavor-A reproducer shape). -/
example (s : PartialState) (P : Prop)
    (R₁ R₂ R₃ R₄ R₅ R₆ R₇ R₈ R₉ : Assertion)
    (h : (R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆ ** R₇ ** R₈ ** ⌜P⌝ ** R₉) s) :
    (R₉ ** R₈ ** R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆ ** R₇) s := by
  drop_pure h
  xperm_hyp h

/-- 10-atom chain, pure as the trailing leaf (depth 9). -/
example (s : PartialState) (P : Prop)
    (R₁ R₂ R₃ R₄ R₅ R₆ R₇ R₈ R₉ : Assertion)
    (h : (R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆ ** R₇ ** R₈ ** R₉ ** ⌜P⌝) s) :
    (R₉ ** R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆ ** R₇ ** R₈) s := by
  drop_pure h
  xperm_hyp h

/-- 10-atom chain with three pures spread across early, middle, and
    trailing positions. -/
example (s : PartialState) (P Q R : Prop)
    (A₁ A₂ A₃ A₄ A₅ A₆ A₇ : Assertion)
    (h : (⌜P⌝ ** A₁ ** A₂ ** A₃ ** ⌜Q⌝ ** A₄ ** A₅ ** A₆ ** A₇ ** ⌜R⌝) s) :
    (A₇ ** A₁ ** A₂ ** A₃ ** A₄ ** A₅ ** A₆) s := by
  drop_pure h
  xperm_hyp h

end EvmAsm.Rv64.Tactics.DropPureTests
