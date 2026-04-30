/-
# `xperm_partial` — design note (slice 1 of #156, REVISED)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file is a DESIGN-ONLY survey + design note. It does NOT yet implement
anything. The original draft (committed in slice 1, evm-asm-a7k) contained
a separation-logic flaw flagged in beads `evm-asm-esr`; this revision
documents the flaw, re-evaluates the design, and recommends scope changes
for slice 2 (`evm-asm-cy7`) and slice 3 (`evm-asm-zu8`) accordingly.

## Problem (unchanged)

`xperm` (defined in `EvmAsm/Rv64/Tactics/XPerm.lean`) closes a goal
`⊢ P = Q` where `P` and `Q` are AC-permutations of `sepConj` (`**`) chains
*with the same multiset of atoms*. Its sibling `xperm_hyp h` (in
`Tactics/XSimp.lean`) consumes `h : P s` and closes `⊢ Q s` under the same
"same-multiset" requirement.

This is a deliberate **fail-or-solve** contract: if the two sides differ on
a single atom, `xperm` errors out (`"could not find atom in LHS"` /
`"final atoms don't match"`) rather than producing a partial result. Per
@pirapira's note on #156, that strictness is valuable — it surfaces real
bugs (forgotten atoms, mis-stated frames, wrong opcode pre/post pairs) that
a permissive variant would silently paper over.

#156 asks for a SIBLING tactic that performs the same atom-matching but,
instead of failing on unmatched leftovers, leaves the user the residual
atoms in some form they can dispatch.

## The semantic flaw in the original design

The original draft proposed two variants:

* Variant 1: starting from `h : (R₁ ** … ** Rₙ) s` and goal `Q s` whose
  atoms are a strict sub-multiset of `h`'s, produce a residual hypothesis
  `h_resid : <unmatched-atoms> s` "by `sepConj_mono_left` / `_right`
  monotonicity plus a `sepConjElim_right` projection".
* Variant 2: reshape the goal into `<unmatched-atoms> s` and close the
  matched portion automatically.

Both are unsound on the raw `Assertion`-application semantics
(`Assertion := MachineState → Prop`, `(P ** Q) s := ∃ s₁ s₂, …`):

1. **`sepConj_mono_left/right` are monotonicity, not projection.** They
   accept a pointwise implication `∀ h, P h → P' h` and weaken one factor
   of an existing `**`-chain on the SAME state. They cannot drop a factor
   from the chain.
2. **`sepConjElim_right` does not exist** in `EvmAsm/Rv64/SepLogic.lean`.
   The existing projection is `holdsFor_sepConj_elim_right`, with type
   `(P ** Q).holdsFor s → Q.holdsFor s`. Its input/output use
   `Assertion.holdsFor`, which existentially abstracts over a sub-state
   that the assertion describes — it does *not* operate on the same `s`
   that `(P ** Q) s` does. There is no closed-form `(P ** Q) s → Q s` in
   the library; in general `(P ** Q) s` does not imply `Q s` (it implies
   `Q` on a sub-heap of `s`).
3. As a consequence, Variant 1 cannot be implemented as proposed: the
   step "split via `sepConj_mono_left` to extract `R s`" is not derivable.
4. Variant 2 has the same flaw in the goal direction: rewriting
   `⊢ Q s` into `⊢ <residual-atoms> s` and closing the matched portion
   would require either an `Iff` (which doesn't exist for general
   asymmetric residuals) or a `holdsFor`-mediated reshape that changes
   the goal's type.

The honest statement is: there is no general tactic that, given
`h : P s` and goal `Q s` with `Q`'s atoms ⊊ `P`'s atoms, produces a
plain proof term inhabiting an `Assertion` applied to `s` for the
unmatched residual.

## What IS sound (and what existing tactics cover it)

Three nearby capabilities ARE expressible:

* **In-place weakening** — replace one atom with a strictly weaker atom
  on the same state. `sepConj_mono_left` / `sepConj_mono_right` already
  cover this. The "drop ownership" pattern `regIs r v → regOwn r` is the
  canonical example.
* **Pure-leaf stripping** — peel a `⌜P⌝` factor from a chain. Provided
  by `extract_pure` (#1432) and composed in `xperm_pure` (#1435,
  PR #1483). Pure leaves admit projection `(⌜P⌝ ** Q) s → P ∧ Q s`
  because pure assertions don't constrain the heap.
* **Frame-with-meta-residual** — close `h : P s ⊢ (Q ** ?Frame) s`,
  unifying `?Frame` with the residual atoms. `xcancel`
  (`Tactics/XCancel.lean`) already does this; it does not surface the
  residual as a separate goal but instead consumes it via the
  user-supplied `?Frame` metavariable.
* **`holdsFor`-mediated projection** — `holdsFor_sepConj_elim_right`
  gives `(P ** Q).holdsFor s → Q.holdsFor s`. This is sound but its
  input/output type is `Assertion.holdsFor`, not raw application; it is
  not a drop-in for sites that work with `(P ** Q) s : Prop` directly.

## Re-survey of the original adopters

The original design listed call sites as "obvious adopters". On
re-reading them, none of them are `xperm_partial`-shaped:

1. `EvmAsm/Evm64/Shift/ShlCompose.lean` lines 310–322 / 456–462 /
   755–767 — these are towers of `sepConj_mono_left (regIs_to_regOwn _)`.
   That is *weakening*, not *dropping*. The total atom count before and
   after is identical; only the labels change (`regIs` → `regOwn`). A
   `xperm_partial` that drops atoms would not eliminate this code.
2. `EvmAsm/Rv64/RLP/Phase2LongLoopThree.lean` lines 100–110 and
   `…LoopFour.lean` lines 95–105 — these are five-deep `sepConj_mono_*`
   towers terminating in `((sepConj_pure_right _).1 _).1`. That is
   *pure-stripping*, which `xperm_pure` (#1435) is the right tool for.
3. `EvmAsm/Evm64/Byte/Spec.lean` lines 289–299, 407–417, 780–906,
   938–944 — also pure-stripping, also #1435 territory.

So the slice-1 survey conflated three distinct asymmetries:

* asymmetry-by-weakening (covered by `sepConj_mono_*`),
* asymmetry-by-pure-leaf (covered by `extract_pure` / `xperm_pure`),
* asymmetry-by-residual (genuinely unaddressed — the #156 case).

Concrete sites in the codebase exhibit only the first two. There is no
hand-rolled "drop a resource atom from a chain" pattern in the current
tree; the closest is `xcancel`, which already handles the case via a
unified `?Frame`.

## Revised recommendation

**Defer slice 2 (`evm-asm-cy7`) until a real call site appears.** The
original motivation rested on a survey that conflated weakening and
pure-stripping with residual-dropping. With those reclassified, the
expected adoption (slice 3, `evm-asm-zu8`) shrinks from "~30–60 LoC
removed" to "0 LoC, no current consumer".

If a future call site DOES need to drop a resource atom (i.e. the user
has a hypothesis they no longer want to track and want to keep just the
matched portion), the soundest implementation is **via `holdsFor`**,
not via raw assertion application:

```
syntax "xperm_partial_holdsFor" ident " with " ident : tactic
-- given h : P.holdsFor s and goal Q.holdsFor s
-- with Q's atoms a strict sub-multiset of P's,
-- produce h_resid : <unmatched-atoms>.holdsFor s
-- by chaining holdsFor_sepConj_elim_right after AC normalisation.
```

This is sound because `holdsFor_sepConj_elim_right` exists and has the
right shape (the residual sits on a sub-heap of `s`, which is exactly
what the user wants when they say "I no longer care about that atom").
The surface API would mirror `xperm_hyp`'s but operate on
`Assertion.holdsFor` instead of raw application.

Adopting this would require either lifting raw `(P ** Q) s` hypotheses
into `(P ** Q).holdsFor s` first (most call sites have the raw form;
the bridge lemma is straightforward but requires `compatibleWith`
context). This adds enough friction that we should defer until a
concrete site actually wants the residual rather than weakening or
pure-stripping.

**Action items:**

* Mark `evm-asm-cy7` (slice 2) as blocked-by-design rather than
  ready-to-implement. Re-open with the `_holdsFor` variant scope above
  if a call site appears.
* Mark `evm-asm-zu8` (slice 3) as blocked on `evm-asm-cy7` with the
  expectation that, if `xperm_partial_holdsFor` does land, the only
  natural adopters will be future code, not retrofits — the surveyed
  retrofits are #1435 and `sepConj_mono_*` work, not this.
* Keep this design file in-tree as the historical record for #156 and
  to prevent re-doing the same mis-survey.

## What this revision does NOT propose

* It does NOT propose closing #156. The user-visible request ("residual
  goal containing the unmatched atoms") is still meaningful — the
  conclusion here is just that today's call sites don't exhibit it,
  and the soundest implementation requires a `holdsFor` lift.
* It does NOT subsume `xcancel`. `xcancel`'s `?Frame` metavariable
  shape is already in production (DivMod, EvmWordArith) and remains the
  right tool when the user wants the residual *consumed* rather than
  surfaced.
* It does NOT subsume `xperm_pure` (#1435 / PR #1483) — that handles a
  different asymmetry (pure leaves) and is independently useful.

## Pointer to existing tactic infrastructure (unchanged from slice 1)

If/when a `holdsFor`-based `xperm_partial` is implemented:

* `XPerm.flattenSepConj` already produces the atom list.
* `XCancel.matchGoalAgainstHyp` already does the asymmetric `isDefEq`
  matching.
* The AC-normalisation lemmas (`sepConj_assoc'`, `_comm'`,
  `_left_comm'`, `_emp_left'`, `_emp_right'`) are already enough to
  build the rearrangement proof.
* `holdsFor_sepConj_elim_right` provides the projection step that the
  raw-application variant lacked.

So the implementation cost is moderate; the blocker is genuine demand,
not infrastructure.

-/
