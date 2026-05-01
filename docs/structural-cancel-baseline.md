# Structural cancellation baseline — atom-flattening cost survey (#245)

Status: measurement / no behavioral change. Tracks beads `evm-asm-h04i`
(slice 1 of GH #245).

## What this is

GH #245 proposes a parallel family of cancellation lemmas of the shape
`(A = B) → (C[A] = D[B])` that peel one matched sub-assertion at a
time without flattening to atoms — so 256-bit-word-level and
loop-postcondition-level chunks can stay opaque during reasoning. This
note catalogues where today's atom-flattening cancellation primitives
(`xcancel`, `xperm`, `xperm_hyp`) actually cost us, so slice 2's API
design is anchored in the concrete bottleneck and not in speculative
"all 562 call sites".

It is meant to be read alongside `docs/xperm-scaling-2026.md` (#265
slice 1 / `evm-asm-1bsj`), which already tabulates atom counts and a
stable/changing partition for the same composition sites. This note
adds (i) the `xcancel`-vs-`xperm` split, (ii) the `@[irreducible]`
bundling tax that #245 would let us drop, and (iii) a recommended
pilot site list shared with slice 4.

## Tactic call-site inventory

Ripgrep counts on `EvmAsm/` (excluding tactic implementation files):

| Tactic | Implementation file | User call sites under `EvmAsm/` |
|---|---|---|
| `xcancel <hyp>` | `Rv64/Tactics/XCancel.lean` (112 LoC) | **0** in proofs |
| `xperm` (goal-side perm, no hypothesis) | `Rv64/Tactics/XPerm.lean` | 77 |
| `xperm_hyp <hyp>` (hyp-side perm) | `Rv64/Tactics/XPerm.lean` | **1297** |
| `xperm_partial` (#156 design note) | `Rv64/Tactics/XPermPartial.lean` | 0 — design only, not yet implemented |
| `drop_pure` | `Rv64/Tactics/DropPure.lean` (uses `xcancel` internally) | 0 — not yet adopted in proofs (see `evm-asm-ui7`) |

Conclusion: `xcancel` has **no user call sites** today (`drop_pure` is
its only client and `drop_pure` itself isn't yet adopted — the bug at
`evm-asm-22a` blocks adoption). All real cost lives on `xperm_hyp`'s
1297 invocations plus the `@[irreducible]` workarounds users deploy
*to keep `xperm_hyp` from blowing up*. So #245 should be read as a
proposal to add a *new* hyp-side cancellation tactic, not as a fix to
the existing `xcancel`.

## Atom-flattening cost — top sites

Reusing the bucket counts from `docs/xperm-scaling-2026.md` (counts at
the *largest* compose step in each theorem):

| Atom bucket | Sites | Compile-time pressure | Bundling state |
|---|---|---|---|
| ≤ 8 | ≈ 420 | trivial | none |
| 9–16 | ≈ 110 | "comfortable" | already bundled |
| 17–24 | ≈ 25 | warm | bundled, occasional split |
| 25–35 | ≈ 7 | hot — drives 256× heartbeat sites | heavily bundled, with `split + delta` rituals |

The "≤ 12 changing atoms" finding from `xperm-scaling-2026.md` applies
here too: even at the worst sites, the *changing* portion that a
structural-cancel tactic would still have to handle by isDefEq is
small. That's the design budget for slice 3's prototype.

## The `@[irreducible]` bundling tax

A structural-cancel tactic's biggest direct payoff is letting us drop
`@[irreducible]` markers that exist *purely* to keep `xperm_hyp` from
flattening past a sub-assertion boundary. Counting `@[irreducible]`
attributes in the tree (rg `@\[irreducible\]`):

| Subtree | `@[irreducible]` count | Notes |
|---|---|---|
| `Evm64/DivMod/LoopDefs/Post.lean` | 35 | per-iteration postconditions |
| `Evm64/DivMod/LoopDefs/Bundle.lean` | 14 | scratch-cell bundles for n=1..3 |
| `Evm64/DivMod/Compose/FullPathN1LoopUnified.lean` | 15 | full-path postconditions |
| `Evm64/DivMod/Compose/FullPathN3LoopUnified.lean` | 13 | preloop+loop unified |
| `Evm64/DivMod/Compose/FullPathN4*.lean` | 25 | n=4 paths (3 files) |
| `Evm64/DivMod/Compose/Base.lean` | 12 | shared dispatcher state |
| `Evm64/EvmWordArith/Div128NoWrapDischarge.lean` | 14 | non-trivial — algebraic, not perm-driven |
| `Evm64/DivMod/SpecCallAddbackBeq/AlgDefs.lean` | 19 | mostly compose-driven |
| `Evm64/DivMod/Spec/{CallSkip,V4,Base,Dispatcher}.lean` | 22 | compose-driven |
| RLP `Phase2Long*` (15 files) | 21 | all chain-length bundles |
| Other | ≈ 70 | mixed |
| **Total** | **287** | |

Of these, the OPCODE_TEMPLATE.md and AGENTS.md notes already flag the
DivMod `LoopDefs/Post.lean` and the `Compose/FullPath*` clusters as
"bundled because `xperm_hyp` cost without bundling exceeds heartbeat
budget". A conservative estimate from inspection:

- ≈ 130 `@[irreducible]`s exist *only* to keep `xperm_hyp` cheap and
  could be dropped once a structural-cancel tactic is available.
- ≈ 70 are algebraic / spec-shape opacity (e.g. `Div128NoWrapDischarge`,
  `AlgDefs`'s ALG-prefix definitions): these would *not* be unlocked
  by #245 and stay opaque on purpose.
- ≈ 60 are mixed — `LoopDefs/Bundle.lean`, `Compose/Base.lean` — these
  bundle scratch-cell state for both readability and perm-cost reasons
  and would need case-by-case judgement.

The "≈ 130 unblocked" figure is the upstream payoff of the
slice 5 (`evm-asm-ompq`) drop-bundling phase.

## Recommended pilot site (shared with slice 4 / `evm-asm-bluw`)

`EvmAsm/Evm64/DivMod/LoopComposeN3.lean`'s
`divK_loop_n3_max_skip_skip_spec_within` (line 106). Reasons:

1. Already the chosen pilot site in #265 slice 3 (`evm-asm-57l1`) and
   #245 slice 4 (`evm-asm-bluw`) — keeping all three slices on the
   same site lets us compare the chunked-`xperm_hyp` and
   structural-cancel approaches head-to-head against a fixed baseline.
2. Hyp-side and goal-side atom counts are mid-range (≈ 35 atoms each
   from `xperm-scaling-2026.md` Site 1) — small enough that prototype
   iteration is cheap, large enough that a heartbeat improvement is
   measurable.
3. The pre-rewrite phase (`u_j1_*_eq_j0_*`, `n3_ub*_off*`, `jpred_1`)
   is canonical: structural cancellation lemmas can match the
   *post-rewrite* shape directly, sidestepping the #265 partition step.
4. If structural-cancel halves heartbeats here, it more than halves
   them at the n=4 PhaseAB site (Site 2) and the
   FullPathN3LoopUnified preloop+loop site (Site 3) where the
   stable/changing ratio is even more favourable.

## Aggregate baseline

For #245's design discussion in slice 2 (`evm-asm-0qba`):

- ≈ 160 `xperm_hyp` sites in the 17+ atom range stand to benefit.
- ≈ 130 `@[irreducible]` markers are direct candidates for drop after
  structural-cancel lands.
- The "changing" atom-set across all hot sites stays ≤ 12 even at the
  worst compose, so the lemma family can be kept small (peel-one-atom
  rules + a small frame builder; no full canonicalisation).
- `xcancel` itself sees no proof-script use today; structural-cancel
  should land as a *new* tactic (`xcancel_struct` or similar) rather
  than retrofitting `xcancel`. The existing `xcancel` keeps serving
  `drop_pure`'s narrow needs.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
