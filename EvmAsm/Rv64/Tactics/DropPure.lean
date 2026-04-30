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

open Lean Elab Tactic

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

/-- `drop_pure h` strips every `⌜P⌝` leaf from the `**`-chain in `h`'s
    type and rebinds `h` to the bare resource tail.

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
      -- Step 1: bubble every pure leaf into a left `And`. Same simp
      -- set as `extract_pure`, but with `sepConj_pure_right` swapped
      -- for `sepConj_pure_right_swap` so trailing pures also land on
      -- the LEFT of the resulting `And`. This makes the `.2` loop
      -- below uniform regardless of where the pure originally sat.
      -- `try` so a bare-resource hypothesis (no pures, possibly no
      -- `**`) is left untouched.
      evalTactic (← `(tactic|
        try
          simp only
            [ ← EvmAsm.Rv64.sepConj_assoc'
            , EvmAsm.Rv64.Tactics.sepConj_pure_right_swap
            , EvmAsm.Rv64.sepConj_pure_left
            , EvmAsm.Rv64.Tactics.sepConj_pure_mid_left
            , EvmAsm.Rv64.Tactics.sepConj_pure_mid_right
            , EvmAsm.Rv64.sepConj_emp_left'
            , EvmAsm.Rv64.sepConj_emp_right'
            ] at $h:ident))
      -- Step 2: peel `And`s off the front of `h` until none remain.
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

end EvmAsm.Rv64.Tactics.DropPureTests
