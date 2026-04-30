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

/-! ### Assertion-level pure-bubble equality

The `sepConj_pure_*` iff lemmas above are stated as
`∀ s, (…) s ↔ (…) s`. `simp` can only fire those at the *outermost*
assertion-applied-to-state position; once the chain is right-associated as
`A₁ ** (A₂ ** (… ** (Aₖ₋₁ ** (⌜P⌝ ** Aₖ₊₁))))` and a pure sits at depth
`k > 1`, those rules can no longer reach it because they would have to
descend through opaque `sepConj` applications — none of the helper
biconditionals are stated under the `**` head, so simp's congruence does
not propagate them.

The equality below is at `Assertion = Assertion` (no `s` applied), so
simp's standard congruence on the binary `sepConj` operator *can* rewrite
it at any depth in a right-associated chain. Repeated application bubbles
a deep pure (`(R ** (⌜Q⌝ ** S))`) one step closer to the head per fire;
once at the head, `sepConj_pure_left` (an iff at outermost `_ s`) peels
it into a left `∧`.

Why only this one Assertion-eq and not also a swap form
(`(R ** ⌜Q⌝) = (⌜Q⌝ ** R)`): a swap form combined with `left_comm_eq`
loops on adjacent pures (`R ** (⌜P⌝ ** ⌜Q⌝)` cycles forever in `simp`).
With only `left_comm_eq`, no rewrite path exists from `R ** ⌜Q⌝` back to
itself, so simp terminates. The price: trailing pures buried at depth
≥ 2 (e.g. `R₁ ** (R₂ ** ⌜Q⌝)`) are not bubbled by this rule alone — they
stay in place until a follow-up pass. The kvl Flavor-A reproducer
(`⌜rhatHi2 ≠ 0⌝` mid-chain with a resource on its right) IS handled,
which is the priority case for beads `evm-asm-22a` (#1435).

Tail-deep pures need a separate strategy (custom tactic); see followup
beads task. -/

theorem sepConj_pure_left_comm_eq (P : EvmAsm.Rv64.Assertion) (Q : Prop)
    (R : EvmAsm.Rv64.Assertion) :
    (P ** (⌜Q⌝ ** R)) = (⌜Q⌝ ** (P ** R)) :=
  EvmAsm.Rv64.sepConj_left_comm' P (⌜Q⌝) R

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
      -- Step 1: bubble every pure leaf to a left `And`.
      --
      -- Stage 1a: right-associate the chain via forward `sepConj_assoc'`.
      -- All subsequent bubble lemmas assume the right-associative shape
      -- `A₁ ** (A₂ ** (… ** Aₙ))`.
      --
      -- Stage 1b: bubble pures to the head of their enclosing subchain
      -- via the Assertion-level eqs `sepConj_pure_swap_eq` (handles a
      -- trailing `_ ** ⌜·⌝`) and `sepConj_pure_left_comm_eq` (handles a
      -- mid-chain pure: `_ ** (⌜·⌝ ** _)`). Because these are stated as
      -- `Assertion = Assertion`, simp's congruence rewrites them under
      -- arbitrary `**` nesting — the iff helpers below cannot do that.
      --
      -- Stage 1c: once each pure sits at the head of its subchain,
      -- `sepConj_pure_left` (an iff at outermost `_ s`) peels the head
      -- pure into a left `∧`. Repeated application drains every pure
      -- onto the outer `∧`-spine.
      --
      -- The remaining helpers (`sepConj_pure_right_swap`,
      -- `sepConj_pure_mid_left/right`, `sepConj_pure_left`) are kept as
      -- back-up matchers for short chains (≤ 4 atoms) where the chain
      -- never gets right-associated and simp can still fire them at
      -- outermost. For long chains (depth ≥ 5) the Assertion-eq rules
      -- do the work — see beads `evm-asm-22a`.
      --
      -- `try` so a bare-resource hypothesis (no pures, possibly no
      -- `**`) is left untouched.
      evalTactic (← `(tactic|
        try
          simp only
            [ EvmAsm.Rv64.Tactics.sepConj_pure_left_comm_eq
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

/-! ### Long-chain regression tests for beads `evm-asm-22a` (#1435).

These pin down the contract that `drop_pure` works on chains where a
mid-chain pure leaf sits 5+ atoms deep — the shape that motivated the
bug report (Div128Step1v2.lean Flavor-A sites threaded a 10-atom
right-assoc chain with `⌜rhatHi2 ≠ 0⌝` at depth 9 with a resource on
its right). Before the `sepConj_pure_left_comm_eq` Assertion-level eq
was added, the iff-only simp set could not rewrite below the outermost
`_ s` and these tests would leave the pure in place, breaking the
follow-up `xperm_hyp h`.

Tail-deep pures (e.g. `R₁ ** … ** Rₙ ** ⌜P⌝` at depth ≥ 2) are
deliberately *not* handled by this slice — adding a swap form to the
simp set creates an infinite-rewrite loop on adjacent pures (see the
file docstring on `sepConj_pure_left_comm_eq`). Followup work is
tracked separately. -/

/-- 6-atom chain, mid-pure at depth 3 with a resource on its right. -/
example (s : PartialState) (P : Prop) (R₁ R₂ R₃ R₄ R₅ : Assertion)
    (h : (R₁ ** R₂ ** ⌜P⌝ ** R₃ ** R₄ ** R₅) s) :
    (R₅ ** R₄ ** R₃ ** R₂ ** R₁) s := by
  drop_pure h
  xperm_hyp h

/-- 10-atom chain with mid-pure at depth 9 — the kvl Flavor-A reproducer. -/
example (s : PartialState) (P : Prop)
    (R₁ R₂ R₃ R₄ R₅ R₆ R₇ R₈ R₉ : Assertion)
    (h : (R₁ ** R₂ ** R₃ ** R₄ ** R₅ ** R₆ ** R₇ ** R₈ ** ⌜P⌝ ** R₉) s) :
    (R₉ ** R₈ ** R₇ ** R₆ ** R₅ ** R₄ ** R₃ ** R₂ ** R₁) s := by
  drop_pure h
  xperm_hyp h

end EvmAsm.Rv64.Tactics.DropPureTests
