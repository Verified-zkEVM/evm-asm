/-
# `xperm_partial` — design note (slice 1 of #156)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file is a DESIGN-ONLY survey + design note. It does NOT yet implement
anything (slice 2, beads `evm-asm-cy7`, will land the implementation; slice 3,
`evm-asm-zu8`, will adopt it at call sites).

## Problem

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

But there are call sites where the user *knows* an atom is unmatched and
just wants the residual obligation as a goal so they can dispatch it
separately. Today those sites either:

* Hand-build a `sepConj_mono_left` / `sepConj_mono_right` tower to manually
  peel the unmatched atom off the hypothesis, then run `xperm_hyp` on the
  resource-only tail. See `EvmAsm/Evm64/Shift/ShlCompose.lean:316–322,
  456–462, 760–767` (5–7-deep `mono_right` towers) and
  `EvmAsm/Rv64/RLP/Phase2LongLoopThree.lean:107–108` /
  `…LoopFour.lean:100`.
* Sidestep the tactic completely with raw
  `(congrFun (show _ = _ from by xperm) h).mp …` plus a separate
  `sepConj_pure_right` / `sepConj_mono_right` extraction (see
  `EvmAsm/Evm64/Byte/Spec.lean:289–299, 407–417, 780–906, 938–944`).

The shape of these sites is uniform: hypothesis side has *strictly more*
atoms than goal side; the user wants `xperm` to consume the goal atoms
out of the hypothesis and hand back a hypothesis (or sub-goal) for the
residual.

## Relationship to existing tactics

* **`xperm`** (`Tactics/XPerm.lean`) — strict `LHS = RHS`. Will stay strict.
* **`xperm_hyp`** (`Tactics/XSimp.lean`) — strict `h : P s ⊢ Q s`. Stays
  strict.
* **`xcancel`** (`Tactics/XCancel.lean`) — closes `h : P s ⊢ (Q ** ?Frame) s`,
  unifying `?Frame` with the residual atoms and *closing the goal*. This is
  the closest cousin to what #156 asks for, but it requires the goal to
  *already mention* a `?Frame` metavariable inside the `**` chain. The new
  tactic targets the case where the goal does NOT mention `?Frame` and the
  user wants the residual atoms surfaced as a *new sub-goal*, not unified
  away.
* **`extract_pure`** (`Tactics/ExtractPure.lean`, #1432) — peels pure leaves
  (`⌜·⌝`) from a hypothesis. Orthogonal: pure atoms participate in
  permutation, but unmatched-on-purpose atoms in #156 are typically
  resource leaves (`↦ᵣ`, `↦ₘ`, `regOwn`, etc.), not propositions.
* **`xperm_pure`** (#1435, design note in `XPermPure.lean`, slice 2 in
  `evm-asm-8py`) — composes `extract_pure` with `xperm_hyp`. Also
  orthogonal: it strips the *pure* asymmetry, not arbitrary atom
  asymmetry.

## Proposed shape: `xperm_partial`

Two viable surface syntaxes, both targeting "consume goal atoms from
hypothesis, leave the residual":

### Variant 1 — produce a residual hypothesis

```
syntax "xperm_partial" ident " with " ident : tactic
-- xperm_partial h with h_resid
-- semantics:
--   given h : (R₁ ** R₂ ** ... ** Rₙ) s and goal Q s,
--   if Q's atoms are a strict sub-multiset of h's atoms,
--   replace h with h_resid : <unmatched-atoms> s
--   and the original goal stays open (caller dispatches manually).
```

This matches the most common pattern in the surveyed call sites: the user
wants the residual as a *fact* they can pass to a downstream tactic
(`xperm_hyp`, `xcancel`, hand-written term).

### Variant 2 — produce a residual sub-goal

```
syntax "xperm_partial" ident : tactic
-- xperm_partial h
-- semantics:
--   given h : P s and goal Q s with Q atoms ⊊ P atoms,
--   reshape goal into <unmatched-atoms> s and close the original
--   matched portion automatically.
```

This is closer to the #156 wording ("leaves a residual goal containing
the unmatched atoms"). Cleaner when the user wants to feed the residual
straight into another tactic via `<;>`.

**Recommendation: implement Variant 1 first.** It composes more cleanly
with the existing toolbox (`xperm_partial h with h2; xperm_hyp h2`) and
mirrors the manual `sepConj_mono_right`-tower pattern that the call sites
already use, so adoption (slice 3) is mechanical. Variant 2 can be added
later as sugar (`xperm_partial h ≡ xperm_partial h with h; show … s; …`)
if a need arises.

## Implementation plan (slice 2, evm-asm-cy7)

Reuse `XPerm.flattenSepConj` + `XCancel.matchGoalAgainstHyp` (already do
exactly the asymmetric `isDefEq`-matching this needs). The new code:

1. Flatten hypothesis and goal sides via `flattenSepConj`.
2. Match goal atoms against hypothesis atoms (`matchGoalAgainstHyp` from
   `XCancel.lean`, but adapted: no `?Frame` metavariable expected on the
   goal side).
3. Compute `residual := unmatchedAtoms hypAtoms matchedIndices`.
4. Build the residual assertion `R = a₁ ** … ** aₖ` via
   `XCancel.buildSepConjChain residual`.
5. Build a permutation proof `P = (matched-chain) ** R` via
   `buildPermProof` (using the existing `sepConj_assoc' / _comm' /
   _left_comm'` machinery).
6. Use `mkEqMP` + `congrFun` to produce a term of type `(matched ** R) s`,
   then split via `(sepConj_mono_left _).2.2` (or `sepConjElim_right`)
   to extract `R s`.
7. Add it as a hypothesis under the user-supplied name, leave the
   original goal untouched.

No new lemmas needed in `SepLogic.lean` — `sepConj_assoc' / _comm' /
_left_comm' / _emp_left' / _emp_right'` are already enough.

## Failure modes

* **Goal atom not found in hypothesis** → throw `"xperm_partial: goal
  atom has no match in hypothesis"`. Same fail-fast contract as
  `xperm` for this direction.
* **Hypothesis atom count < goal atom count** → throw `"xperm_partial:
  hypothesis has fewer atoms than goal; use xperm or xcancel"`.
* **Empty residual** (sizes equal, all atoms matched) → behave like
  `xperm_hyp`: just bind `h_resid : empAssertion s` and finish. (Or
  alternatively warn + delegate to `xperm_hyp`. Decide in slice 2.)

## Survey of likely adopters (slice 3, evm-asm-zu8)

Concrete sites that today hand-build a `sepConj_mono_*` tower or an
explicit `(congrFun (show _ = _ by xperm) _).mp` and would shrink to one
`xperm_partial h with h'` line:

1. `EvmAsm/Evm64/Shift/ShlCompose.lean:760–767` — 6-deep nested
   `sepConj_mono_right` chain peeling six atoms before `xperm_hyp`.
2. `EvmAsm/Evm64/Shift/ShlCompose.lean:316–322, 456–462` — 1-deep
   `sepConj_mono_left (regIs_to_regOwn …)` plus `xperm_hyp`. Less of a
   win but still removes one layer.
3. `EvmAsm/Rv64/RLP/Phase2LongLoopThree.lean:107–108` and
   `…LoopFour.lean:100` — 5-deep `sepConj_mono_right` chains.
4. `EvmAsm/Evm64/Byte/Spec.lean:289–299, 407–417, 780–783, 900–906,
   938–944` — pure asymmetry; better handled by `xperm_pure` (#1435)
   than `xperm_partial`. Listed for completeness, NOT a target for
   slice 3 of #156.

Approximate impact on slice 3: ~30–60 LoC removed from Shift and RLP
files, plus a readability win (a 7-line nested `mono_right` tower
becomes one line). The Byte/Spec sites belong to #1435, not this
issue.

## What this design does NOT cover

* **Bidirectional asymmetry** — i.e. *goal* has atoms not in the
  hypothesis. Symmetric to the case `xperm_partial` handles, but the
  semantics ("introduce a sub-goal asking the user to prove the missing
  atom") is meaningfully different. Defer until a real call site
  appears; today every surveyed asymmetric site has hyp ⊋ goal, never
  goal ⊋ hyp.
* **Multi-atom partial unification** — i.e. unification of goal atoms
  against hypothesis atoms via metavariables. `xcancel` already covers
  the single-`?Frame` case; multi-mvar matching can be added later
  via `xperm_partial` if the need ever arises.
* **Pure atoms** — covered by `xperm_pure` (#1435), not this issue.

-/
