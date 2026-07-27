# GuestLayout parameterisation measurement (GH #10753 / `evm-asm-8fz1p`)

Branch: `perf/guest-layout-param-prototype`. Measured against `origin/main`
`aff464653`. Host: shared 32-core; all lake timings with
`LAKE_ARTIFACT_CACHE=false`. One lake driver at a time.

## Population check (coord's numbers, re-verified on `origin/main`)

| Pattern | Count (this session) | Coord quoted |
|---|---|---|
| `jalOff GuestAddrs` | **161** | 162 |
| `laHi GuestAddrs` | 141 | 141 |
| BOTH | 118 | 118 |

Query used here: `git grep -l 'jalOff GuestAddrs' origin/main -- 'EvmAsm/Codegen/'`.
Off-by-one on jalOff vs coord’s 162 — second independent count; not investigated
further (one file likely matched a different pattern or ref). BOTH=118 agrees.

Most GuestAddrs importers are **mixed** (difference + absolute). A
reference-form split would not decouple modules; parameterisation is the
right lever. Prototype module: `BloomAddValue.lean` (mixed, outside BAL /
do-not-touch).
## Prototype shape

- `EvmAsm/Codegen/GuestLayout.lean` — hand-written structure (3 fields used
  by BloomAddValue) + `GuestLayout.zero`.
- `EvmAsm/Codegen/GuestLayoutInstance.lean` — `guestLayout` from `GuestAddrs`
  (top-level only; the only module that may import the generated table for
  this path).
- `bloomAddValue_prog (L : GuestLayout)` — no `GuestAddrs` import.
- Probe split to `BloomAddValueProbe.lean` so the leaf does not pull
  `HashBridge` (which still imports `GuestAddrs`).
- Emission / `_eq_prog` / length guard use `.zero` (reloc path keeps `la`/`jal`
  symbolic). Image table applies `guestLayout`.

Import closure of `BloomAddValue`: **9 modules**, **`GuestAddrs` absent**.

## 1. Elaboration time (module force-rebuild ×3)

| Condition | Built line |
|---|---|
| Before (`origin/main` shape, still imports GuestAddrs+HashBridge) | 260–265 ms |
| After (parameterised, GuestAddrs-free) | 255–260 ms |

No material elab regression on the 3-field prototype. (Earlier noisy
330–450 ms samples under load; settled force-rebuilds match baseline.)

## 2. Invalidation — module **count** (decisive; clock is noisy)

Synthetic: flip `GuestAddrs.bav_hash` `0xab2a0150 → 0xab2a0158`, then
`lake build EvmAsm.Codegen.Programs.BloomAddValue`.

| | Modules rebuilt | BloomAddValue.olean |
|---|---|---|
| **Before** | **3** (`GuestAddrs`, `HashBridge`, `BloomAddValue`) | **changed** |
| **After** | **0** | **unchanged** (same sha256 / ino / mtime) |

Control after param: `lake build GuestLayoutInstance` rebuilds **2**
(`GuestAddrs`, `GuestLayoutInstance`) — only the instance layer.

Mechanism demonstrated: layout regen no longer invalidates the parameterised
program module.

## 3. Guard cost

`_prog` is a function. Guards apply a concrete layout:

- `#guard (bloomAddValue_prog .zero).length = 45`
- `_eq_prog` / emission string still keyed on **emitted string** with
  `emitProgramR … bloomAddValue_relocs` (symbolic `la`/`jal`) — unaffected.

No new identifier-keyed guards. Cost is one `.zero` (or `guestLayout`)
application site per guard / image row.

## 4. Granularity microbench (full-table scale)

Local scripts under `bench/guest_layout/` (not part of the EvmAsm lake lib;
run with `lake env` `LEAN_PATH`). Structure type + `zero` instance +
`laHi`/`laLo`/`jalOff` `decide` example.

### Flat structure — **negative at full scale**

With `maxRecDepth 8000`:

| Fields | Approx elab |
|---|---|
| 500 | ~2.4 s |
| 800 | ~6–8 s |
| 1000 | ~17 s |
| 1100 | ~14–17 s |
| **1125** | **heartbeat timeout** (`isDefEq` / missing projections) |

Without raised rec depth, 1125 fails earlier on `maxRecDepth`. A named
closed `zero` value at 500 fields also hit compiler IR
`constructor has too many fields` in an earlier AsmReloc-coupled microbench.
**A single flat `GuestLayout` with ~1125–3000 fields is not viable.**

### Nested structure-of-structures — **works**

| Shape | Approx elab (type + zero + decide sample) |
|---|---|
| Nested1125, groups of 25 | ~1.11 s |
| Nested1125, groups of 50 | ~1.04 s |
| Nested3089, groups of 50 | ~3.18 s |
| Nested3089, groups of 100 | ~2.83 s |

Recommend for full rollout: structure-of-structures grouped like RegionMap
(or `Symbol → Nat` over a small inductive). Prototype 3-field path is fine
and already proves the invalidation win.

### Nested field-access cost at the consumer (the rollout-pay question)

Question: does Nested3089 elaboration recur per importer, or is it paid once
in the layout module?

Method: type-only `NestedLayoutType3089` (31 groups × ≤100 fields, **no**
zero instance) built once; BloomAddValue-shaped consumer uses
`L.g0.f0` / `L.g0.f1` / `L.g0.f2` in the same `laHi`/`laLo`/`jalOff` sites
(no concrete mega-zero — emission stays a function of `L`). Control: identical
consumer on a 3-field flat layout. Force-rebuild consumer ×5 with type olean warm
(`lean` direct, `LEAN_PATH` includes `bench/guest_layout`).

| Module | Force-rebuild wall (×5) |
|---|---|
| NestedLayoutType3089 (type only, cold) | **~4.95 s** once |
| Consumer + Nested3089 access (type warm) | **0.29–0.34 s** |
| Consumer + flat-3 access | **0.28–0.29 s** |

**Access is free within noise.** The nested type cost is paid once in the layout
module; importers do not re-pay Nested3089 elaboration for field projection.
Rollout arithmetic: one ~5 s type module vs 141 modules no longer rebuilding on
address-table regen — straightforwardly worth it. Grouping may still follow
RegionMap for human navigation; it is **not** required to keep per-importer
structures small for elab cost.

## `LAYOUT_PROGS` allowlist end state

`scripts/guest_image_coverage.py` maps layout-parameterised `_prog` names to
`… guestLayout` applications. **Fail-closed:** omit a converted name → type
error at the image table, not a silent wrong row.

**End state:** once every linked `_prog` is parameterised, the allowlist is
deleted and the generator applies `guestLayout` (or the nested instance)
**unconditionally**. The allowlist is a transitional artifact only; it must not
outlive the migration.

## Rollout intent (for coord)

This PR is the **reference implementation + measurement**, not a half-migration
to leave stranded. Follow-on (same lane if assigned): land nested `GuestLayout`
type module; convert Programs in batches; delete `LAYOUT_PROGS` when the last
row flips; keep `GuestLayoutInstance` as the sole `GuestAddrs` consumer for
converted programs. One-module dual-convention on main is acceptable only while
that follow-on is owned — otherwise park the branch as docs-only evidence.

## Decision for #10753

| Claim | Result |
|---|---|
| Parameterisation stops GuestAddrs regen from rebuilding the program module | **Yes** (0 vs 3 modules; olean stable) |
| 3-field prototype elab cost | **Neutral** (~same ms) |
| Flat ~1125-field structure | **Negative — do not ship** |
| Nested ~1125 / ~3089 | **Positive — viable** (~1 s / ~3 s type+zero) |
| Full 141-module conversion | **Not measured** (one-module prototype only) |
| End-to-end regen-cycle wall time | **Not measured** |

**Recommendation:** keep the idea; do **not** land a mega-flat structure.
Expand via nested groups (or inductive map). Convert modules callee-first /
mixed-reference leaves as capacity allows; keep `GuestLayoutInstance` as the
sole GuestAddrs consumer for converted programs.

## What this PR contains vs not

**Contains:** type + instance + BloomAddValue conversion + probe split +
generator hook for layout-applied progs + this note.

**Does not contain:** full-table nested layout; Tasks 2–3; regen-cycle
automation; bench oleans.
