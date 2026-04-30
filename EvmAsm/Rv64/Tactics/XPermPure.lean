/-
# `xperm` / `xperm_hyp` and pure assertions — design note (slice 1 of #1435)

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).

This file is a DESIGN-ONLY survey + design note. It does NOT yet implement
anything (slice 2, beads `evm-asm-8py`, will land the implementation; slice 3,
`evm-asm-ag3`, will adopt it at call sites). Closely related to #1432 /
`extract_pure` (`EvmAsm/Rv64/Tactics/ExtractPure.lean`); this note explicitly
calls out where the two should compose vs. where `xperm` itself needs a
pure-aware mode.

## Problem

`xperm` (and its `xperm_hyp` cousin in `Tactics/XSimp.lean`) AC-normalizes a
`sepConj` chain on each side and then closes the goal/hypothesis by matching
atoms hash-by-hash. Pure-atom leaves (`⌜P⌝`, defined in `Rv64/SepLogic.lean`
as `pure (P : Prop) : Assertion`) participate in this match exactly like
resource atoms — but they aren't actually about the heap, they're propositions
lifted into the assertion language.

This causes friction at call sites where the pure leaves on the two sides are:

* **Identical and in the same position** — `xperm_hyp` works fine. (Most call
  sites, e.g. all of `Phase2LongLoop*.lean`.)

* **Identical but rearranged** — `xperm_hyp` still works because it AC-normalizes.
  Also fine.

* **Asymmetric** — only one side has the pure atom (or the two sides have
  *different* pure props, with one logically implying the other). This is the
  painful case: callers either drill the pure out manually with
  `obtain ⟨_, _, _, _, _, hrest⟩ := …` chains (see #1432 / `extract_pure`)
  or they hand-build a `sepConj_mono_right` tower to drop the pure leaf
  before invoking `xperm_hyp`, or they sidestep `xperm_hyp` entirely and
  spell out `(congrFun (show _ = _ from by xperm) h).mp hp` plus a separate
  `(sepConj_pure_right h).1 hp |>.1`.

## Survey of call sites (2026-04-30)

`xperm` / `xperm_hyp` is invoked in ~200 places across the codebase. The
overwhelming majority do not interact with `⌜·⌝` at all: e.g. every
`Phase2LongLoop{Two..Eight}.lean`, every `Lt/Gt/Or/Sgt/.../Spec.lean`, the
`Tactics/LiftSpec.lean` macro itself. These are pure resource-atom permutations
and are not relevant to this issue.

The interesting sites — where pure assertions live in the same `**` chain as
resource atoms that `xperm_hyp` is asked to permute — fall into three flavors:

### Flavor A: pure atom drops out (asymmetric end)

Caller has a hypothesis `(R₁ ** ... ** Rₙ ** ⌜P⌝) s` and wants to feed it to a
goal `(Rπ(1) ** ... ** Rπ(n)) s` (no pure). Today: build a `sepConj_mono_right`
tower to peel `⌜P⌝` off, then `xperm_hyp` the resource-only tail.

Representative sites:

1. `EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean:420-428` — 8-deep
   `sepConj_mono_right` chain dropping `⌜rhatHi2 ≠ 0⌝` before `xperm_hyp hP'`.
2. `EvmAsm/Evm64/DivMod/LimbSpec/Div128Step1v2.lean:465-475` — sibling case,
   same shape, dropping `⌜rhatHi2 = 0⌝`.
3. `EvmAsm/Evm64/DivMod/LimbSpec/Div128Step2.lean:~456` and `~500` — same
   8-deep tower pattern, mirror lemmas.
4. `EvmAsm/Evm64/DivMod/LimbSpec/Div128Clamp.lean`, `Div128ProdCheck1.lean`,
   `Div128ProdCheck1b.lean`, `Div128ProdCheck2.lean`, `Div128Step2v4.lean`
   — same family, several occurrences each.

These sites are also called out by #1432 / `extract_pure` slice 1, but from
the other direction (extracting the *value* of `P`, not just dropping it).
The two issues meet here: `extract_pure h` introduces `h_pure : P` and rebinds
`h` to the resource-only tail — which is exactly the input that a pure-stripped
`xperm_hyp` would also produce.

### Flavor B: pure atoms accumulate asymmetrically (frameR + weaken)

Caller has `(R ** ⌜P⌝) → (R' ** ⌜Q⌝)` where `R, R'` permute via `xperm` and
`P → Q` is provable directly (typically `Q = P ∧ … ∧ … ` with the extra
conjuncts coming in via `cpsBranch_frameR (⌜…⌝)`). Today: split the post-
condition rewrite into two halves — `xperm` (or `(congrFun (show _ = _ by
xperm) _).mp`) on the resource side, `(sepConj_pure_right h).1 hp |>.1` on
the pure side.

Representative sites:

5. `EvmAsm/Evm64/SignExtend/Compose.lean:484-491` — `cs1_framed` builds
   `cs1_clean ** ⌜v5 ≠ 0⌝`, then `cpsBranchWithin_weaken` is forced to do
   `xperm` *and* a manual `sepConj_pure_right` extraction in two separate
   closure arguments (one per branch leg) because the pre/post pures don't
   line up.
6. `EvmAsm/Evm64/SignExtend/Compose.lean:520-528` — same shape, `cs2_framed`.
7. `EvmAsm/Evm64/Byte/Spec.lean:289-299`, `407-417`, `780-783`, `900-906`,
   `938-944` — repeated `(congrFun (show _ = _ from by xperm) h).mp hq` next
   to a separate pure-extraction line. ~5 instances in this file alone.
8. `EvmAsm/Evm64/Shift/ShlCompose.lean:316-322`, `456-462`, `767` — same
   pattern, copied across the SHL composition variants.

### Flavor C: pure atoms passed through unchanged (false alarms)

Some sites carry `⌜P⌝` in *both* the hypothesis and the goal, in different
positions. `xperm_hyp` already handles this — the pure atom is just one more
hash to permute. We surveyed these but they are not motivating examples.
Example: `EvmAsm/Rv64/RLP/Phase2LongLoopBody.lean:208,213` (both pre and post
of the BNE branching closure carry the pure atom; `xperm_hyp` runs on each
side once).

## Decision: option (b) — sibling tactic, not (a) preprocessing

We considered three designs:

(a) **Preprocess inside `xperm` itself.** Strip pure leaves from both sides
    before AC-normalizing, run the resource permutation, re-attach pure leaves
    afterwards via `decide`/`assumption`. Rejected: silent strip-and-reattach
    changes the closing tactic's contract and would make Flavor C sites slower
    for no benefit (they already work). It would also make debugging "why
    didn't `xperm` close?" harder when the failure is on the pure side.

(b) **Sibling tactic `xperm_pure` that wraps `extract_pure` + `xperm`.** This
    composes the existing #1432 work cleanly: `xperm_pure h` first invokes
    `extract_pure h` (introducing `h_pure_1, h_pure_2, …` from the LHS),
    then runs `xperm_hyp h` on the resource-only tail, then closes any
    `⌜·⌝` atoms remaining on the goal side via `decide` / `assumption` /
    `tauto` over the introduced pures. **This is the recommended option.**
    It keeps `xperm` simple, gives users explicit control at problem sites,
    and benefits from any future improvement to `extract_pure`.

(c) **Documented combinator only.** Just write the recipe in `XPerm.lean`'s
    docstring and tell users to spell it out. Rejected: Flavor B sites
    *already* spell it out (5–8 lines each, 15+ instances) — the value of
    a tactic over a combinator is precisely to delete those lines.

Slice 2 (`evm-asm-8py`) will implement `xperm_pure` along these lines:

```
syntax "xperm_pure" ident : tactic
-- semantics:
--   xperm_pure h
--   ≡ (extract_pure h with ⟨..⟩;     -- intro h_pure_*, rebind h to resource tail
--      xperm_hyp h                     -- permute resource side
--      <;> first | assumption | decide | tauto)
--                                       -- close any ⌜·⌝ on the goal side
```

Slice 3 (`evm-asm-ag3`) will rewrite the Flavor-A and Flavor-B sites listed
above. Approximate impact: ~25 lines deleted per Flavor-A site (× ~7 sites)
and ~5 lines per Flavor-B site (× ~15 sites); total ~250 LoC removed, plus a
significant readability win for the DivMod / Shift / SignExtend Compose files.

## What this design does NOT cover

* **Pure atoms inside `cpsTriple` codomains** that are *not* the immediate
  argument of `xperm_hyp` — those are out of scope; they're a `weaken` /
  `seq_frame` problem, not a permutation problem.
* **Multi-state pure atoms** like `⌜∀ s, …⌝` — not observed anywhere in the
  current codebase, deferred until a real use case appears.
* **Replacing `extract_pure`.** `xperm_pure` is a *composition*, not a
  replacement; `extract_pure` will still be the right tool when the user
  wants the pure value but does not want to permute the resource tail.
-/
