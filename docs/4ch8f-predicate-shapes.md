# Separation-logic predicate shapes (structures that stay)

Proof-lane input. **Landing structural changes is a prerequisite for
separation-logic proofs; the other half is the predicate shapes themselves.**
This document records shapes for structures that are **not** scheduled to change
tonight, so the proof lane can start without re-deriving them.

**Template** (uniform; from `#11186` + slot nine / `#11222`):

1. **BASE, EXTENT**, and whether **capacity × stride = extent EXACTLY**
2. **THE ENTRY** — every field, offset, width
3. **COUNT / CURSOR** — where it lives; live entries vs high-water mark
4. **VALIDITY** on entry `i` — sorted / unique / initialised / monotone / **nothing**
5. **OWNERSHIP AND LIFETIME** — per-tx or per-block; who resets; when
6. **DISJOINTNESS** — what may alias; **union children are where naive sep fails**
7. **SLOT NINE — INITIALISATION CONTRACT** — which cells must be zero on entry to
   which routine; what breaks if not; which entry points audited
8. **BUILD UNIT** — a predicate that does not name its unit is false in at least
   one image (`#11222`)

**Rule: the base is an input, never a literal.**
`slot(p) = arena_base + p × 0x19000` is a theorem about any image; baking
`0xad3dd5e0` into the statement goes false on the next deletion. RegionMap pins
are drift guards for one build, not predicate constants.

**Reference image** (illustrative addresses only): main `6b75068fe`, guest sha256
`07f36a6d7f778fc15b06d969f8dc929d375a296e2012404db3b6eae5bbe8d097`. Cite symbols
and structural constants; do not copy absolute bases into Lean predicates.

Related:

- `docs/4ch8f-region-map.md` — layout inventory
- `docs/4ch8f-dispatch-journal-initialization.md` — twelve DJ-* cells (`#11227`)
- `#11233` close — `teer_success_table` STAY + predicate (included below for one set)
- `#11222` — `baap_storage_values` three sizes across units

---

## 1. `call_frame_arena` (frame control slots)

| slot | value |
|---|---|
| **Build unit** | `stateless_guest` (RegionMap `frameRuntimeRegions`) |
| **Base** | **input** `callFrameArenaBase` / symbol `call_frame_arena` (== `basr_values`) |
| **Extent** | `frameArrayBytes = frameSlotCount × frameStride` |
| **Capacity × stride** | `1025 × 0x19000 = 104_960_000` — **EXACT** |
| **Entry** | one frame slot = `0x19000` (102400) bytes of control + scratch layout (see CallFrameLayout); not a homogeneous record array for BAL |
| **Index** | `slot(p) = arena_base + p × 0x19000` where **`p` = pre-increment `evm_call_depth` (PARENT depth)**. Child at depth `d ∈ 1..1024` uses slot `d−1 ∈ 0..1023`. Depth 0 never `call_frame_enter` — no arena slot |
| **Count/cursor** | `evm_call_depth` (global); not a table count |
| **Validity** | distinct depths ⇒ distinct slots by arithmetic (no maintained sorted invariant) |
| **Lifetime** | nested call tree within a tx; enter on descend, reclaim on `frame_return` |
| **Disjointness** | **UNION umbrella**: five children tile the **front** of the arena (see §2). Arena extent is `max(frame need, children tiling)`; children are **not** additional RAM. Naive “arena + baap_storage_values” double-counts |
| **Spare** | **slot 1024 never reached** (1025 allocated, 1024 usable) — state it |
| **Init (slot 9)** | slots are written on enter; do not assume whole arena zero. Per-field init is CallFrameDescend / snapshot path |
| **Unclean note** | reachable depth under 63/64 gas is ≪ 1024; capacity is spec STACK_DEPTH_LIMIT shaped, not gas-tight |

---

## 2. Union children of `call_frame_arena` (Phase-H / BAAP front)

Arena-relative (layout-invariant). From `RegionMap.dataUnionChildren`:

| name | off | size | capacity × stride |
|---|---:|---:|---|
| `basr_values` | 0 | `basrArenaBytes` | state-change × encoded-account |
| `basr_accounts` | `basrArenaBytes` | same | same |
| `baap_storage_desc` | `2·basrArenaBytes` | `bsrMaxBalItems × 40` | **100000 × 40 = 4_000_000 EXACT** |
| `baap_storage_paths` | after desc | `bsrMaxBalItems × 64` | **100000 × 64 = 6_400_000 EXACT** |
| `baap_storage_values` | after paths | `bsrMaxBalItems × 64` | **100000 × 64 = 6_400_000 EXACT in guest emit formula** |

**Trailing pad** after children up to `frameArrayBytes` is **anonymous** (no symbol). Extent-to-next-symbol on `baap_storage_values` can charge the pad to that name — **do not treat next-symbol extent as allocation** (`#11186` correction).

**Disjointness among children:** pairwise by construction (`dataUnionChildren_pairwise_disjoint`).  
**Aliasing with frames:** children **share bytes** with the frame array (phase-indexed use). Separation must be **phase-split** (CallFramePhase / anyBytes views), not “child disjoint from arena”.

---

## 3. `baap_storage_values`

| slot | value |
|---|---|
| **Build unit** | **MUST NAME UNIT** — see unclean finding |
| **Base** | **input** — symbol `baap_storage_values` (union child; absolute = `callFrameArenaBase + off`) |
| **Guest extent (formula)** | `bsrMaxBalItems × bsrPathBytes` = 100000 × 64 = **6_400_000** — **EXACT** vs formula |
| **Entry** | **variable-length** RLP/encoded storage value blobs packed by **byte cursor**, not fixed 64 B records. Paths are fixed 64 B in `baap_storage_paths`; values are sequential bytes |
| **Cursor** | `baap_storage_value_cursor` (u64) — **high-water byte pointer** into the values arena; reset to base at apply entry (`BalAccountApplyPostFields`) |
| **Count** | descriptors in `baap_storage_desc` / path index carry (ptr, len) pairs — live descriptor count is phase-local, not a single global live-entry count for values |
| **Validity** | **no alignment invariant** on values (byte-range only). No global sort on the values blob |
| **Lifetime** | block-root / BAAP apply phase; not a per-tx journal |
| **Disjointness** | **union child** of `call_frame_arena` — aliases frame slots by phase; aliases sibling baap_* by offset partition only |
| **Init (slot 9)** | cursor set to base at apply entry (**self-discharged**); values content overwritten as encoded; do not require pre-zero of full 6.4 MiB for correctness of encoding |
| **UNIT-LOCAL EXTENT `#11222`** | same symbol name is emitted by three units: guest and `BalAccountApplyPostFields.lean` probe both use **`bsrMaxBalItems × bsrPathBytes` = 6_400_000**; `BalAccountDescriptorArray.lean` remains **32_768**. A predicate `extent = 100000×64` is true in the guest and BAAP probe and **false** in the descriptor probe. **Do not land a predicate without naming the build unit.** Closing `#11222` (overload vs dead) is required before a single global claim |

---

## 4. `evm_memory_pool` (shared nested-frame EVM memory)

| slot | value |
|---|---|
| **Build unit** | `stateless_guest` (RegionMap `evmMemoryPoolRegion`) |
| **Base** | **input** `evmMemoryPoolBase` / symbol `evm_memory_pool` (immediately after `call_frame_arena_end`) |
| **Extent** | `evmMemoryPoolBytes` = **96 MiB** = 100_663_296 — guest |
| **Capacity × stride** | **not** a fixed-record table; LIFO byte arena for live EVM memory across nested frames. Gas-bounded live total via `MemoryBudgetGuard` (`maxTotalLiveMemoryBytes`) |
| **Entry** | N/A (byte pool). Per-frame windows are slices; reclaim on return |
| **Cursor / ownership** | per-frame base/limit in call-frame control; pool is LIFO shared |
| **Validity** | live windows disjoint by construction of enter/return pairing (scoper: disjointness falls out of address formula + parent depth indexing for **frame** slots; pool windows are separate) |
| **Lifetime** | per nested call; reclaimed on `frame_return` |
| **Disjointness** | **pairwise disjoint** from `call_frame_arena` as whole regions (`frameRuntimeRegions_pairwise_disjoint`). Not a union child of the arena |
| **Init (slot 9)** | do not assume pool zero; frames write their windows. Depth-1 reset paths restore limits |
| **UNCLEAN / multi-unit** | `CallFrameDescend.lean` probe emit uses `.zero 0x100000` (1 MiB) under the same symbol name — **another unit-dependent size**. Predicate must name `stateless_guest` / RegionMap extent |

---

## 5. `callee_seed_table` (+ `callee_seed_count`)

BAL-sourced nested-callee SLOAD seed (`#11176` / F3). **Stays until `#10651` authority switch dissolves the need** — not a free delete (consumer live on main `6b75068fe`).

| slot | value |
|---|---|
| **Build unit** | `stateless_guest` |
| **Base** | **input** symbol `callee_seed_table` |
| **Extent** | `calleeSeedTableBytes = calleeSeedTableCap × calleeSeedEntryBytes` |
| **Capacity × stride** | **128 × 96 = 12_288 — EXACT** (`#guard` in BlockVerdictParams) |
| **Entry (96 B)** | |
| | `+0..31` — addrHash / exec-log account key (LE limbs, 32 B) |
| | `+32..63` — storage slot key **LE-limb** (BE key byte-reversed on write) |
| | `+64..95` — value **LE-limb** (BE reversed from header / or direct from block map) |
| **Count** | `callee_seed_count` (u64) — **live entry count** (not high-water past deleted holes); zeroed at `seed_callee_storage` entry |
| **Validity** | **nothing global** (no sort/unique required for seed correctness). Duplicates harmless (cold seed; runtime overlay wins). Order = BAL account walk × slot walk |
| **Lifetime** | **per-tx**: produced in `dispatch_tx_runtime_code` → `seed_callee_storage`; consumed once in `runtime_dispatcher_call` seed loop (copy into live exec log `@0xa0630000` + `exec_log_seed_flag=1`); count zeroed next producer entry |
| **Disjointness** | standalone BSS; not in call_frame union. Scratch `csce_keys` (100000×32) is separate producer scratch |
| **Init (slot 9)** | `callee_seed_count = 0` on entry to `seed_callee_storage`. Table body may be stale past count — readers must use count. Consumer: if count=0 skip loop |
| **Consumers** | (1) `runtime_dispatcher_call` copy loop; (2) no other writers of table rows found. SPIKE_BREAK `seed_callee_storage` HIT on fixture 00103 |
| **Guards** | capacity full → `a0=1` fail-closed (`#11157`) |
| **Related** | `exec_log_seed_flag` parallel array marks seeded exec-log rows (block/tx capture skips seed_flag≠0) |

---

## 6. `teer_success_table` (+ `teer_success_count`) — STAY / converged

Full close write-up: `#11233`. Spec counterparts: `written_accounts` + `delegation_set_for` inside `set_delegation`.

| slot | value |
|---|---|
| **Build unit** | `stateless_guest` |
| **Base** | **input** `teer_success_table` |
| **Extent** | 1060 × 32 = **33_920 — EXACT** |
| **Entry (32 B)** | `+0..19` authority address BE; `+20..23` u32 `AUTH_BASE_charged` (0/1); `+24..31` pad |
| **Count** | `teer_success_count` — **live entries**; zeroed at `eip7702_auth_state_prepare` entry |
| **Validity** | linear membership by address; no sort required |
| **Lifetime** | per-tx prepare walk; does not survive txs |
| **Disjointness** | standalone |
| **Init (slot 9)** | count=0 on prepare entry; word@+20=0 on append |
| **Consumers** | (1) prepare — ACCOUNT_WRITE / AUTH_BASE once; (2) **`extcodehash_at_header_state_root`** — if match and word@+20≠0 → EMPTY_CODE_HASH |
| **Full** | count≥1060 → prepare fail-closed |

---

## 7. Runtime-dispatch journal scalars (twelve + retained)

**Authoritative table:** `docs/4ch8f-dispatch-journal-initialization.md` (`#11227` / `#11152`).

Summarised for the uniform set:

| slot | value |
|---|---|
| **Build unit** | `stateless_guest` |
| **Base** | **each cell is its own symbol** — no single arena; bases are inputs |
| **Extent** | each cell **8 B** (u64) |
| **Capacity × stride** | N/A (scalars) |
| **Entry** | the u64 value itself |
| **Count** | N/A |
| **Validity** | **zero on dispatcher entry** (the invariant) |
| **Lifetime** | one user or system `runtime_dispatcher_call` invocation |
| **Disjointness** | not members of frame pool or baap union |
| **Init (slot 9)** | **this is the whole contract** — `emitRuntimeDispatcherCallableSetup` zeros DJ-01..DJ-12 before readers run. Audited entry: every `runtime_dispatcher_call` (user + system re-entry). Exception: `destroyed_count`/`overflow` **survive** system re-entry (`#11147`) — **outside** the twelve wipe set |
| **Retained not deleted** | `evm_selfdestruct_staged`, `cd_destroyed_empty_hits` still wiped; SPIKE absence ≠ deletion proof |
| **Gated outside table** | `exec_code_effect_{count,next,overflow}` when `code_state_mtx_active` |

IDs DJ-01..DJ-12: `evm_refund_acc`, `evm_selfdestruct_seen_count`, `evm_selfdestruct_seen_overflow`, `create_nonce_table_count`, `create_nonce_table_overflow`, `create_nonce_undo_count`, `account_state_pending_count`, `account_state_created_count`, `account_state_delete_count`, `account_state_overflow`, `evm_log_data_used`, `evm_log_data_overflow`.

---

## 8. Structures that cannot carry a clean predicate yet (findings)

These are **findings**, not documentation gaps:

| structure | why unclean | action |
|---|---|---|
| `baap_storage_values` (cross-unit) | three extents for one name (`#11222`) | resolve overload vs dead before any `extent=` theorem |
| `evm_memory_pool` (cross-unit) | guest 96 MiB vs probe 1 MiB emit | name unit in every claim |
| F3 seed path as a whole | still BAL-sourced; load-bearing until `#10651` | do not prove “exec log = post-state” while seed injects declared BAL |
| S3 `exec_code_effect_log` auth append | still BAL-finals gated (`#11234`) | same authority switch |
| Anonymous arena pad after baap children | next-symbol extent lies | never use next-symbol size as allocation |

---

## 9. How to use this in Lean

1. Parameterise `arena_base`, `pool_base`, table bases as arguments or `GuestAddrs`-style defs read from the image under test — **not** hexadecimal prose.
2. State `capacity * stride = extent` as a `decide`/`native_decide`-free kernel fact from the same constants `BlockVerdictParams` / RegionMap use.
3. For union children, open a **phase** hypothesis before claiming exclusive ownership of bytes.
4. For DJ-* cells, the opening lemma of a dispatcher triple is `cell = 0` (or the `#11147` exception list).
5. Never identify `baap_storage_values` extent without `unit := stateless_guest` (or the probe unit under test).

---

## Provenance

Composed from:

- scoper `#11186` pool/arena/union measurements and corrections (base symbolic; `p` = parent depth; baap values 6.4 MiB not 35 MiB pad)
- `#11222` three-size `baap_storage_values`
- `#11227` / `docs/4ch8f-dispatch-journal-initialization.md`
- `#11233` teer_success STAY + EXTCODEHASH consumer
- F3 chain on main `6b75068fe` (seed_callee SPIKE_BREAK HIT; consumer `runtime_dispatcher_call`)
- RegionMap `dataUnionChildren`, `frameRuntimeRegions`, BlockVerdictParams callee seed caps
