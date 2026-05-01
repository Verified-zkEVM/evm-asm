# Chunked `xperm_hyp` — API surface and tactic shape (#265 slice 2)

Status: design note / no Lean changes. Tracks beads `evm-asm-hnub`
(slice 2 of GH #265). Reads on top of
`docs/xperm-scaling-2026.md` (slice 1 / `evm-asm-1bsj`) and
`docs/structural-cancel-design.md` (#245 slice 2 / `evm-asm-0qba`).

## Goal

Specify the tactic that slice 3 (`evm-asm-57l1`) prototypes on
`EvmAsm/Evm64/DivMod/LoopComposeN3.lean`. Working name: `xperm_chunked`
(also acceptable: `xperm_hyp_chunked`).

The tactic must (a) accept the same hypothesis-rewrite semantics as
`xperm_hyp` so existing call sites can migrate by a one-token rename,
(b) discharge the *stable* portion of the chain in O(n) using
syntactic / hash equality, and (c) fall through to the existing
`xperm_hyp` builder on the small *changing* residual so correctness is
inherited from the proven prover.

`xperm_chunked` is a sibling of `xperm_hyp`. It does *not* replace the
flatten-based prover; it pre-shrinks its input.

## Why a partition tactic, not a fresh prover

Three constraints argued for staying inside the flatten-based pipeline:

1. **Correctness inheritance.** The atom-permutation builder in
   `EvmAsm/Rv64/Tactics/XPerm.lean` (`bringToFrontProof`,
   `permProofChain`, AC-rewrite normalisation) is well-tested across
   ~560 call sites. A new prover would re-litigate that.
2. **Pre-rewrite phase compatibility.** All hot sites already do
   `simp only [divmod_addr, …]; rw [u_j1_*_eq_j0_*, jpred_1, …]`
   immediately before `xperm_hyp`. Those rewrites make the stable atoms
   *syntactically* equal on both sides — exactly the fast-match
   precondition we want. We must consume that work, not reproduce it.
3. **Failure surface.** Slice-1 baseline counted ≤ 12 changing atoms at
   every hot site. The flatten-based prover is fast on ≤ 12 atoms;
   only the stable portion is the bottleneck. Eliminating the stable
   portion in O(n) is the entire payoff — no need to swap algorithms
   on the changing portion.

Decision: implement as a pre-pass that strips matched stable atoms
from both sides, then delegates to the existing `xperm_hyp` builder on
the residual. The driver is small (≈ 80 lines of MetaM) and reuses
`flattenSepConj`, `findAtomIdx`, `bringToFrontProof`,
`permProofChain` from `XPerm.lean`.

## Tactic surface

```text
xperm_chunked <hyp>
xperm_chunked <hyp> only        -- skip residual fallback (debug)
xperm_chunked <hyp> with strict -- partition by syntactic eq only
                                 -- (no hash, no isDefEq) — debug
```

Default mode (no flags): hash-based partition + isDefEq-on-collision
fallback inside the partition + flatten-based `xperm_hyp` builder on
the residual. This is the only mode adopted at call sites; the flags
exist purely for the slice-3 prototype's measurement runs.

Semantics in default mode:

1. Read `hyp : H s` and goal `⊢ G s`. If they parse identical via
   `parseSepConj?`/`isDefEq` already, close and return.
2. Flatten both sides via `flattenSepConj` (same routine as
   `xperm_hyp`).
3. **Partition step (new):** for each atom in the goal-side list,
   compute its `Expr.hash` and look up the hypothesis-side atom array
   by hash. On a hash match, confirm via *syntactic* equality
   (`Expr.eqv` or `Expr.equal`) — *not* `isDefEq`. Atoms that match
   syntactically are dropped from both lists in lockstep.
4. **Residual prover:** if the residual lists are non-empty, call the
   existing `xperm_hyp` permutation builder on them. The builder
   returns a proof term `(L₁ ** … ** Lₖ) s ↔ (R₁ ** … ** Rₖ) s` where
   `Lᵢ`/`Rᵢ` are the unmatched atoms.
5. **Re-assemble:** rebuild the proof of the original goal by:
   - Applying `sepConj_assoc'` / `sepConj_left_comm'` rewrites that
     rotate the matched atoms to the head on both sides (the
     equivalence is `(stable ** residualHyp) ↔ (stable ** residualGoal)`).
   - Discharging the residual half via the prover from step 4.
   - The stable half is closed by `rfl` because the partition used
     syntactic equality.
6. On failure (residual prover fails): fall back to the original
   `xperm_hyp` on the *unpartitioned* chain. This keeps adoption
   safe: any site that goes wrong with `xperm_chunked` retries with
   the proven prover at zero correctness risk. The cost is one extra
   parse and partition pass, ≈ a few ms.

### Why syntactic equality, not `isDefEq`, for the partition

The slice-1 baseline shows that pre-rewrites already make stable
atoms syntactically identical on both sides. Hash + syntactic
comparison is O(n); `isDefEq` per pair is O(n²) with deep WHNF
reduction — the very cost we are trying to avoid. If a stable atom
fails the syntactic check it falls into the residual and the
existing `xperm_hyp` handles it via `isDefEq` as today. We never
miss matches; we just sometimes pay the same O(n²) cost as today on
a smaller residual, which is still a strict win.

The `with strict` flag (no hash bucket, just `Expr.eqv`) is for
slice-3 measurement: it lets us isolate "how much of the speedup is
from hash bucketing alone" from "how much is from skipping isDefEq".

### `only` flag: residual-disabled debug mode

`xperm_chunked hp only` partitions and asserts that the residual is
empty (otherwise it errors out with the residual lists shown). Used
during slice-3 development to verify the partition correctly
identifies the stable portion at each site. Not for production use.

## Interaction with existing tactics

| Situation | Recommended primary tactic |
|---|---|
| Both sides ≤ 8 atom chain (per-instruction step) | `xperm_hyp` (existing) |
| 9–16 atoms, mostly stable cells, post-rewrite | `xperm_chunked` (this slice) |
| 17–35 atoms, large stable bundle + small changing tail (LoopComposeN3, FullPathN3LoopUnified, PhaseAB n=4) | `xperm_chunked` (primary win) |
| Hypothesis carries pure leaves | `drop_pure` (existing), then `xperm_chunked` or `xperm_hyp` |
| Goal has sub-assertion provably equal to hyp's via equation lemma | `xcancel_struct … with <eq lemma>` (#245 slice 3), then `xperm_hyp`/`xperm_chunked` on residual |

`xperm_chunked` and `xcancel_struct` are siblings, not competitors:

- `xperm_chunked` exploits **syntactic equality** of stable atoms
  after pre-rewrites. It is fast when the proof author has already
  rewritten the chain into a state where most atoms are
  syntactically aligned.
- `xcancel_struct` exploits **opaque sub-assertion bundles** that
  appear in both sides as a single atom (e.g.
  `loopIterPostN3Max_da …`). It peels them via equality-congruence
  without flattening into the bundle.

A site that has both a stable cell-cluster *and* an opaque bundle
chains them: `xcancel_struct` first to peel the bundle, then
`xperm_chunked` on the cell-cluster residual. Slice 4
(`evm-asm-bluw`) is the head-to-head measurement that picks the
default for LoopComposeN3 sites.

## Where `xperm_chunked` does *not* help

Three classes of sites where the partition pre-pass adds rewrite
overhead with no payoff:

1. **Per-instruction proofs (≤ 8 atoms).** Total cost is dominated by
   the `parseSepConj?`/`flatten` pass that both prover variants pay.
   Partitioning saves nothing because there is no stable bulk to
   strip. Keep `xperm_hyp` here.
2. **Heavily-permuted small chains where every atom is in the
   changing set.** Rare in DivMod (the `Add`/`Sub`/`Mul` opcode files
   under `EvmAsm/Evm64/`); also keep `xperm_hyp`.
3. **Sites already using `@[irreducible]` bundling that drops the
   chain to ≤ 16 atoms.** Slice 5 (`evm-asm-ompq`) is the followup
   that drops the bundling at sites unblocked by `xperm_chunked` — at
   that point those sites become candidates for `xperm_chunked`. But
   until slice 5 lands they are already cheap and no migration is
   needed.

## Acceptance for slice 2 (this note)

- Design note merged at `docs/chunked-xperm-design.md`.
- No Lean changes.
- Slice 3 (`evm-asm-57l1`) implements `xperm_chunked` per this design
  in `EvmAsm/Rv64/Tactics/XPermChunked.lean`, with a fallback to
  `xperm_hyp` on partition or residual-prover failure.
- Slice 4 (`evm-asm-aezw`) broadens adoption to
  `FullPathN3Loop.lean` and `Compose/PhaseAB.lean` once slice 3's
  measurement on LoopComposeN3 confirms the predicted ≥ 2× speedup
  on the 17–35 atom bucket.

## Implementation sketch (for slice 3)

The driver lives in a new file
`EvmAsm/Rv64/Tactics/XPermChunked.lean`, imported from
`EvmAsm/Rv64/Tactics.lean` after `XPerm`. Public surface:

```lean
namespace EvmAsm.Rv64.Tactics

/-- Hash-partition + flatten-based residual prover.
    Same semantics as `xperm_hyp`; faster when stable atoms dominate. -/
syntax (name := xpermChunked) "xperm_chunked" term : tactic

@[tactic xpermChunked] def evalXPermChunked : Tactic := …
```

Internals reuse `flattenSepConj`, `findAtomIdx`,
`bringToFrontProof`, `permProofChain` from `XPerm.lean`. Net new code
≈ 80 lines: partition routine + residual-assembly proof builder +
fallback wrapper.

The fallback wrapper is the safety net:

```lean
def xpermChunkedCore (hyp : Expr) : TacticM Unit := do
  try
    partitionAndProve hyp     -- the new path
  catch e =>
    trace[Meta.Tactic] "xperm_chunked: falling back to xperm_hyp ({e.toMessageData})"
    xpermHypCore hyp          -- the existing prover
```

So even if the partition logic has a corner-case bug, no site will
break — it just runs at the original speed.

## Out of scope for slice 3

- Goal-side variant (`xperm_chunked` on goal-only). The `_hyp`
  shape is the only one used at the hot sites.
- Automatic detection of which sites benefit. Slice 4 picks them by
  hand from the slice-1 baseline.
- A `@[xperm_chunked_atom]` attribute for marking known-stable
  atoms. Not needed: hash + syntactic equality finds them.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
