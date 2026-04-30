# Split plan: `EvmAsm/Evm64/DivMod/Spec/CallAddback.lean`

Tracking: GH issue #1078, beads `evm-asm-ry8` (parent) / `evm-asm-av8` (this doc).

## Status

| File | Current lines | Cap | Over by |
|------|---------------|-----|---------|
| `EvmAsm/Evm64/DivMod/Spec/CallAddback.lean` | **3850** | 1500 | 2350 |

(Note: the `evm-asm-ry8` description quotes 5324 lines from a stale inventory; the
file has shrunk since then but still substantially exceeds the cap.)

## Inventory by region

The file currently contains 37 top-level declarations. Reading top-to-bottom:

| Lines | Block | Top-level decls | Theme |
|-------|-------|-----------------|-------|
| 1–96  | imports, namespace, prelude comments | — | |
| 97–151 | `n4CallAddbackBeqSemanticHolds` | 1 def | semantic predicate definition (referenced everywhere) |
| 153–1318 | **v2 numerical bounds (untruncated)** | 12 thm | `div128Quot_v2_*` bounds on the 2-stage normalization quotient: q1''≤q1', q1''_dLo_no_wrap, rhat'<2dHi, rhat''<2^33, toNat_eq_strict, un21_toNat / un21_toNat_case, knuth_compose_qHat_vTop_le_nat_v2, qHat_vTop_le (untruncated + full), le_val256_div_plus_two, le_5limb_shifted variant |
| 1319–2627 | **v2 runtime-conditioned bounds** | 7 thm | `*_under_runtime` variants discharging phase-1 / no-wrap / un21<vTop / qHat·b > a / qHat lower bound from runtime hypotheses (`hb3nz`, `hborrow_v2`) — these are what the call+addback BEQ stack spec actually uses |
| 2628–2779 | **predicate def-equation + stack spec** | 3 thm | `n4CallAddbackBeqSemanticHolds_def`, `n4_call_addback_beq_div_mod_getLimbN`, `evm_div_n4_call_addback_beq_stack_spec` |
| 2781–3014 | **qHat = div+1 / div+2 bridges** | 2 thm | `qHat_eq_div_plus_one_of_single_addback`, `qHat_eq_div_plus_two_of_double_addback` (consume the v2 bounds, produce equational facts about `qHat`) |
| 3016–3849 | **alg-bundle euclideans + amod-pow-s wrappers** | 9 thm | `algCallAddbackBeq_*` lemmas: `addback_combined_euclidean_carry2`, `mulsub_euclidean`, `amod_pow_s_lt_pow256`, `mulsub_euclidean_double`, `c3_n_eq_u4_plus_one_of_single_addback`, `algCallAddbackBeqMsC3_eq_u4_plus_one_of_single_addback`, `post1_eq_mod_times_pow_s_of_c3_eq_u4_plus_one`, `post1_val_eq_amod_pow_s_pure_nat`, `algCallAddbackBeqPost1Val_eq_amod_pow_s_of_single_addback` |

## Proposed split (4 files)

The file has a clean dependency chain top-to-bottom: each block consumes only
results from blocks above it. We can extract three sibling files behind the
existing umbrella:

| New file | Source range | Approx lines | Content |
|----------|--------------|--------------|---------|
| `Spec/CallAddback/V2Bounds.lean` | 1–1318 (header carved) | ~1300 | pure / untruncated Word bounds on `div128Quot_v2`: `q1''_le_q1'`, `q1''_dLo_no_wrap`, `rhat'_lt_2dHi_under_guard`, `rhat''_lt_pow33`, `toNat_eq_strict`, `un21_toNat`/`_case`, `knuth_compose_qHat_vTop_le_nat_v2_untruncated`, `un21_toNat_untruncated`, `qHat_vTop_le_full`/`_untruncated`, `le_val256_div_plus_two`/`_untruncated`, `le_5limb_shifted_div_plus_two_untruncated`. No runtime hypotheses — purely arithmetic. |
| `Spec/CallAddback/V2RuntimeBounds.lean` | 1319–2627 | ~1310 | `*_under_runtime` variants: `phase1c_in_knuth_range`, `phase1_div_invariant`, `knuth_A`, `phase1_no_wrap_lo`, `un21_lt_vTop`, `qHat_mul_b_shifted_gt_a_shifted`, `qHat_gt_q_true_shifted`, `qHat_lower_shifted`. Imports V2Bounds. |
| `Spec/CallAddback/AlgEuclideans.lean` | 3016–3849 | ~835 | algorithmic-bundle euclideans + `amod_pow_s` wrappers used by the `c3 = u4 + 1` / `qHat = div + 1` rewrite paths in the addback-BEQ pipeline. Imports V2RuntimeBounds (transitively) for the constants it threads. |
| `Spec/CallAddback.lean` (kept) | 1–96 prelude + 2628–3014 | ~480 | semantic predicate `n4CallAddbackBeqSemanticHolds`, `n4_call_addback_beq_div_mod_getLimbN`, `evm_div_n4_call_addback_beq_stack_spec`, and the `qHat_eq_div_plus_{one,two}` bridges. Re-exports `V2Bounds`, `V2RuntimeBounds`, `AlgEuclideans` so existing `import EvmAsm.Evm64.DivMod.Spec.CallAddback` consumers do not have to change their imports. |

### Why the V2Bounds / V2RuntimeBounds boundary

Lines 153–1318 prove pure / untruncated Word bounds on `div128Quot_v2` with no
runtime predicates — they take `b3nz` / wrap hypotheses as ordinary arguments.
Lines 1319–2627 specialize those bounds under runtime predicates derived from
`n4CallAddbackBeqSemanticHolds` (in particular `hb3nz` and `hborrow_v2`). The
split is exactly where the file stops talking about Word arithmetic and starts
threading the runtime-side semantic predicate, so the boundary is natural and
the imports are one-directional.

### Why keeping the `qHat_eq_div_plus_{one,two}` bridges in CallAddback.lean

These two theorems sit between the v2 bounds (which talk about division
quotients in the abstract) and the alg-bundle euclideans (which talk about
`algCallAddbackBeq*` wrappers). They are the bridge consumed by the stack
spec itself, so leaving them adjacent to `evm_div_n4_call_addback_beq_stack_spec`
keeps the stack-spec-facing surface in one place. The trimmed CallAddback.lean
ends at ~480 lines, well under cap.

## PR sequencing

Each move is a self-contained refactor (no semantic changes), so the four
follow-up PRs are independent in difficulty but must land in this order to
keep `import` chains acyclic:

1. **PR-1 — extract `Spec/CallAddback/V2Bounds.lean`** (lines 153–1318).
   Imports CallSkip + CallAddbackPureNat (same set CallAddback.lean already
   imports for that block). CallAddback.lean adds `import …V2Bounds`.
2. **PR-2 — extract `Spec/CallAddback/V2RuntimeBounds.lean`** (lines 1319–2627).
   Imports V2Bounds + CallAddback.lean's runtime-side imports.
3. **PR-3 — extract `Spec/CallAddback/AlgEuclideans.lean`** (lines 3016–3849).
   Imports V2RuntimeBounds (or CallAddback.lean if some of the bridges below
   the cut feed back).
4. **PR-4 — drop `file-size-exception` header** from CallAddback.lean and
   verify `scripts/check-file-size.sh` (or equivalent) is happy. Also register
   the three new files in the Spec umbrella (`EvmAsm/Evm64/DivMod/Spec.lean`).

After PR-1–PR-3, CallAddback.lean is ~480 lines, V2Bounds ~1300, V2RuntimeBounds
~1310, AlgEuclideans ~835. None of these would re-trigger the file-size cap.

## Risks & non-goals

- **No semantic changes.** Each PR is a literal cut-and-paste plus the matching
  `import` line; theorem statements and proofs are unchanged. CI's `lake build`
  is the regression gate.
- **No re-grouping inside blocks.** Some V2Bounds theorems pair with their
  `_untruncated` variants — keeping them together is sufficient; we do not
  attempt to renumber or rename.
- **The `qHat_*_under_runtime_v2` group at lines 2518–2627** is right at the
  V2RuntimeBounds boundary; if any of those are consumed below line 2628 in a
  way that does not flow through V2RuntimeBounds, PR-2 may need to keep them
  in CallAddback.lean instead. The PR author verifies via `lake build`
  before declaring the cut clean.
- **`AlgEuclideans` ordering relative to the `qHat_eq_div_plus_*` bridges**:
  the bridges at 2781–3014 do reference `algCallAddbackBeq*` names from the
  3016+ region in some places (alg-bundle is declared elsewhere; only specific
  derived equalities live at 3016+). PR-3 author confirms direction by trial
  build before cutting.

## Acceptance for `evm-asm-av8` (this doc)

- `docs/divmod-calladdback-split-plan.md` lands on `main` via this PR.
- No Lean changes in this PR.
- Follow-up PRs (`evm-asm-ry8` becomes a series) reference this plan.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
