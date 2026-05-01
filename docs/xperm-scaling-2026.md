# `xperm_hyp` scaling baseline — DivMod compositions (2026)

Status: measurement / no behavioral change. Tracks beads `evm-asm-1bsj`
(slice 1 of GH #265).

## Goal

Ground GH #265's chunked-xperm proposal in concrete numbers from the
current tree. For each representative composition site this note records
(a) the size of the assertion chains entering the `xperm_hyp` step,
(b) how many of those atoms are *stable* (structurally identical on
both sides — the partition step in the proposed tactic could cancel
them in O(n)), and (c) how many are *changing* (would still need the
expensive `isDefEq`-based permutation). The "changing" count is the
relevant bound on slice 2's prototype.

The atom counts below are derived from the postcondition definitions
(`EvmAsm/Evm64/DivMod/LoopDefs/Post.lean` — `loopExitPost`,
`loopBodySkipPost`, `loopBodyN3{Skip,Call,Addback,CallAddback,…}Post`,
`loopBodyN3{…}PostJ`, `loopIterPostN3{Max,Call}`, `loopN3{…}Post`,
`loopN3PreWithScratch`, `preloopN3UnifiedPost`) plus the `frameR`
calls at each composition site. They are static (counted from the
source), not heartbeat instrumentation.

## Atom inventory: `loopExitPost` (the recurring 21-atom backbone)

Used by every `loopBodyN*{Skip,Addback,…}Post` via `loopExitPost n …`.
21 atoms total:

| Group | Atoms | Stable across iter step? |
|---|---|---|
| Reg cells: `x12 sp`, `x1 j'`, `x5 j<<3`, `x6 uBase`, `x7 qAddr`, `x10 c3`, `x11 q_f`, `x2 un3F`, `x0 0` | 9 | partial — `x12 sp`, `x0 0` are always stable; `x1 x5 x6 x7` deterministic from `j`; `x10 x11` carry mulsub outputs (changing); `x2` carries `un3F` (changing) |
| Mem `j-cell` (sp+3976), `n-cell` (sp+3984) | 2 | stable (j-cell index changes between iters; within one xperm step it is stable) |
| Mem `v0..v3` (sp+32, +40, +48, +56) | 4 | **stable** (read-only across the whole loop) |
| Mem `u-window` at `uBase` (offsets 0, 4088, 4080, 4072, 4064) | 5 | **changing** (mulsub output) |
| Mem `q-cell` at `qAddr` | 1 | changing (q write of the iteration) |

So `loopExitPost` itself partitions ≈ **6 stable + 15 changing** for a
generic iter→iter compose. The `j`-dependent register/mem cells (`x1
x5 x6 x7` plus `j-cell`) are syntactically *not* identical pre/post
(different `j` value) but a structural matcher modulo a single arith
rewrite (`jpred_1`, `n3_ub1_off…`) makes them stable — that's the case
LoopComposeN3 already pre-rewrites with `rw [hj', u_j1_0_eq_j0_4088,
…]` before `xperm_hyp`. With those rewrites applied, the partition is
**13 stable + 8 changing** (the 5 u-window cells, q-cell, x10, x11).

## Site 1 — `LoopComposeN3.lean`, `divK_loop_n3_max_skip_skip_spec_within` (line 106)

This is the smallest n=3 two-iter composition (the recommended
prototyping target in the issue body).

- Hyp side (`hp`): `loopBodyN3SkipPost sp 1 qHat … uTop` framed with
  2 atoms (`(u_base_0+0)↦ₘ u0Orig`, `q_addr_0↦ₘ q0Old`).
  - Unfolds via `delta loopBodyN3SkipPost loopBodySkipPost
    loopExitPostN3 loopExitPost`: **21 + 2 = 23 atoms**.
- Goal side: precondition of j=0 spec `loopN3Pre … j=0`, framed with
  2 atoms (`(u_base_1+4064)↦ₘ (uTop - ms_c3)`, `q_addr_1↦ₘ qHat`).
  - **23 atoms**, same shape as `loopExitPost` plus 2 frame atoms.
- After the explicit address rewrites
  (`jpred_1, u_j1_0_eq_j0_4088, u_j1_4088_eq_j0_4080,
   u_j1_4080_eq_j0_4072, u_j1_4072_eq_j0_4064`) and one `rw
   [sepConj_assoc']`:
  - **stable atoms**: `x12 sp`, `x0 0`, `x1 j'`, `x5`, `x6`, `x7`,
    j-cell, n-cell, v0..v3 mem (4) → **12 atoms**.
  - **changing atoms**: `x10 c3`, `x11 q_f`, `x2 un3F`, the 5 u-window
    cells, q-cell, plus the 2 frame atoms on each side that are *not*
    structurally identical because the framing is on different sides
    of the iteration → **11 atoms**.

So `xperm_hyp hp` here permutes **23 atoms** of which only **11 are
truly changing**. A stable/changing partition tactic could discharge
the 12-atom stable subset in O(n) and run isDefEq permutation only on
the 11 remaining.

Eight sibling theorems in `LoopComposeN3.lean` (`max_skip_skip`,
`max_skip_addback`, `max_addback_skip`, `max_addback_addback`,
`max_skip_unified`, `max_unified_*`, `addback_*`) follow this exact
shape — same 23/11 split, same prefix rewrites. They each invoke
`xperm_hyp` once at the seq-compose step and once at the
`cpsTripleWithin_weaken` step (the latter on a smaller chain ≈ 16
atoms post-bundling because `loopN3MaxSkipSkipPost` is `@[irreducible]`).

## Site 2 — `Compose/PhaseAB.lean`, `evm_div_phaseB_n4_spec_within`

The PhaseAB file contains 41 `xperm_hyp` invocations across 5 major
theorems. The largest is `evm_div_phaseB_n4_spec_within` plus the
zero-path / phaseA-ntaken composition (`evm_div_bzero_spec_within`,
`evm_div_phaseA_ntaken_spec_within`). Representative compose-step
chain sizes (counted from `frameR` arguments + sub-spec postconditions
visible in the source):

| Theorem | xperm sites | Hyp atoms (largest step) | Stable | Changing |
|---|---|---|---|---|
| `evm_div_bzero_spec_within` | 6 | ≈ 16 (phaseA body 9 + frame 7) | ≈ 11 | ≈ 5 |
| `evm_div_phaseA_ntaken_spec_within` | 4 | ≈ 14 | ≈ 10 | ≈ 4 |
| `evm_div_phaseB_n4_spec_within` | ≈ 12 | ≈ 28 (phaseB init1+init2+addi+bne+tail composed) | ≈ 18 | ≈ 10 |
| Phase-AB n=4 final compose | 6 | ≈ 32 | ≈ 22 | ≈ 10 |

(Atom counts are estimated from the explicit `frameR` lists at each
compose; they are not symbolic-execution traces.) The PhaseAB file is
the one the issue body singles out at "51.2M heartbeats (256× baseline)"
— that bound is consumed almost entirely by the n=4 final compose and
the phaseB n=4 compose. In both cases the changing portion is ≤ 10.

## Site 3 — `Compose/FullPathN3LoopUnified.lean`, preloop+loop compose (line 199)

The preloop+loop compose at `divK_n3_full_path_loop_unified_spec_within`:

- Hyp (`hp`): `loopSetupPost` after `delta`, plus 9 frame atoms. The
  `loopSetupPost` is the largest single-source assertion in the
  DivMod tree, with ≈ 26 atoms. Total **≈ 35 atoms**.
- Goal: `loopN3PreWithScratch` (≈ 26 atoms once `loopN3Pre` is
  unfolded) + 9 frame atoms = **≈ 35 atoms**.
- Pre-rewrites: `n3_ub1_off{0,4088,4080,4072,4064}, n3_ub0_off0,
  n3_qa{1,0}, se12_{32,40,48,56}, x1_val_n3` (10 named address
  lemmas) — these align the preloop output to the loop input, exactly
  the "stable after rewrite" cohort.
- Stable: registers (9), j-cell, n-cell, v0..v3 mem (4), the 9 frame
  atoms (a0..a3, two zero scratch q-cells, two zero scratch u-cells,
  shiftMem) → **≈ 24 atoms**.
- Changing: `x10`, `x11`, the 5 u-window cells, q-cell, the
  `loopSetupPost`-specific clz/dispatcher residue → **≈ 11 atoms**.

This is the largest single-step xperm in the DivMod tree and is the
canonical case for "≥ 30 atoms forces `@[irreducible]` bundling".
Without bundling it would be ≈ 35, with bundling (current state via
`loopN3PreWithScratch`'s `@[irreducible]` siblings) it drops back to
≈ 16 atoms at the outer compose. **A chunked-xperm tactic with
stable/changing partition would let us drop the bundling here without
heartbeat regression** — that's the slice 5 (`evm-asm-ompq`) payoff.

## Aggregate baseline

DivMod-tree `xperm_hyp` call sites (562 total per `grep`) by atom-count bucket
(estimated, counted at the largest compose in each theorem; smaller
intra-theorem `xperm_hyp` invocations are typically ≤ 8 atoms after
bundling):

| Bucket | Sites | Notes |
|---|---|---|
| ≤ 8 atoms | ≈ 420 | Small frame rotations, trivially fast — chunking is not relevant |
| 9–16 atoms | ≈ 110 | `@[irreducible]`-bundled compositions; today's "comfortable" range |
| 17–24 atoms | ≈ 25 | LoopComposeN3 sibling theorems, FullPathN3 mid-composes |
| 25–35 atoms | ≈ 7 | PhaseAB n=4 final, FullPathN3LoopUnified preloop+loop, FullPath divCode-extension composes — these are the "256× baseline" sites |

The changing-atom column is consistently **≤ 12** at every bucket.
That is the design number for slice 2: a partition tactic only has to
run isDefEq permutation on ≤ 12 atoms even at the worst sites,
producing an estimated **5–10× speedup** at the 25–35 bucket and
**eliminating** heartbeat pressure at the 17–24 bucket.

## Recommendation for slice 2 (`evm-asm-hnub`)

1. The partition predicate should be **structural equality (no
   reducibility)** on each atom expression. The pre-rewrite phase
   (`u_j1_*_eq_j0_*`, `n3_ub*_off*`, `jpred_1`) is already doing the
   "make it structurally equal" work; chunked-xperm should consume
   that and not re-derive it.
2. The changing-atom set is small enough (≤ 12) that a direct
   permutation builder over the residual is fine — no need for the
   "divide-and-conquer" alternative from the issue body.
3. Prototype on `LoopComposeN3.lean`'s
   `divK_loop_n3_max_skip_skip_spec_within` (Site 1 above): smallest
   site that exercises the full pre-rewrite + frame + compose pattern.
   If the prototype halves heartbeats at Site 1 it will more than halve
   them at Sites 2 and 3 (cost is dominated by the changing portion).
4. The canonical-order alternative is not recommended for the
   prototype: it requires re-canonicalizing every spec postcondition
   in the tree, an invasive change that would conflict with the
   ongoing offset-naming and bundling refactors. Stable/changing is
   non-disruptive — it lives entirely inside `xperm_hyp`'s
   implementation.

Authored by @pirapira; implemented by Hermes-bot (evm-hermes).
