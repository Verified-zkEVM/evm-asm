# Authoritative guest region map (bead `evm-asm-4ch8f.6`, mechanical half)

This document reconciles the two memory-layout schemes the stateless guest has
carried unreconciled, records the evidence for every region's extent, and gives
the machine-checked overlap inventory for the one intentional aliasing.

> **Status update (2026-07-05, bead `.6` CLOSED):** the phase-ownership proof
> this doc originally deferred is DELIVERED — `EvmAsm/Rv64/SAsm/PhaseSplit.lean`
> + `EvmAsm/Codegen/CallFramePhase.lean` (#9724, one-resource/two-views model),
> plus the soundness audits in `docs/4ch8f-callframe-audit.md` (#9851). The
> audits found and led to fixing the stride/geometry divergence (beads
> `.71`/`.74`, fixed by #9852 — `CallFrameLayout` re-pinned to the emitted
> `0x39000`/128 KiB geometry, arena resized). Two residual bugs remain open:
> `.72` (child env 552/560) and `.73` (`bv_system_storage_log` is read
> POST-dispatch — the "Phase-H-only" liveness claim below is FALSE for that one
> child; see the audit doc). Numeric snapshot tables in this file may lag the
> ELF — `RegionMap.lean` + `scripts/check-region-map.sh` are the live authority.

Source of truth, in order of authority:

1. **The linked ELF** (`stateless_guest.elf`) — `readelf -S`/`-s`. Final arbiter.
2. **`EvmAsm/Codegen/RegionMap.lean`** — the kernel-checked Lean map. Must match
   the ELF; `scripts/check-region-map.sh` enforces it.
3. The two upstream constant sets it mirrors: `EvmAsm/Stateless/MemoryLayout.lean`
   (Scheme A) and `EvmAsm/Codegen/CallFrameLayout.lean` +
   `.../Programs/BlockVerdictParams.lean` (Scheme B).

Reproduce everything below with one command each:

```
scripts/check-region-map.sh          # ELF vs RegionMap.lean + TSV (drift guard)
lake build EvmAsm.Codegen.RegionMap  # the disjointness/fit/overlap theorems
```

---

## 1. Scheme reconciliation

| | Scheme A (working-RAM anchors) | Scheme B (linked sections) |
|---|---|---|
| Where | `EvmAsm/Stateless/MemoryLayout.lean` | `-Ttext/-Tdata/--section-start` + `.data` labels |
| Window | `0xa0020000 .. 0xa1ba0000` (working RAM below `.data`) | `.text` `0x80000000`; `.data` `0xa3000000`; `.sszscratch` `0xbf500000` |
| Consumer | the **verified stateless port** under `EvmAsm/Stateless/` (the 4ch8f epic target) | the **currently-emitted** `stateless_guest` (Dispatch.lean + BlockVerdict) |
| Prior proof | **none** (sizes implicit in anchor gaps) | fit lemmas for the 3 giant arenas only |

Scheme A is the (largely still-aspirational) map for the in-progress verified
port; Scheme B is what the linker emits today. Crucially they are **not** cleanly
disjoint in the current build — the emitted guest's RV64 call stack (below) lands
inside Scheme A's `execution_witness_area`. So the map is split into two lists:

- **`RegionMap.guestRegionMap`** — the **emitted-reality** map: every byte the
  *currently-emitted* `stateless_guest` actually touches (INPUT, the ZisK system
  band, OUTPUT, the guest call stack, the live state-tracker window, `.text`,
  `.data`, `.sszscratch`). This is what routine triples and wave `.9.3` frame
  against. Proved pairwise disjoint with **no exception list**
  (`guestRegionMap_pairwise_disjoint`) and zone-fitting (`guestRegionMap_fits_ram`).
- **`RegionMap.schemeAAnchors`** — the **aspirational** port contract, kept
  separate, proved internally consistent (`schemeAAnchors_pairwise_disjoint`) but
  NOT merged into the emitted map, because it collides with the stack (§3.1).

### FINDING — Scheme A is almost entirely unreferenced by the emitted guest

A literal + `lui`-immediate scan of the emitted `stateless_guest.s` for each
Scheme-A anchor address:

| anchor | address | refs in emitted guest |
|---|---|---|
| `STATE_TRACKER_AREA` | `0xa0630000` | **17** (live: "persistent/live storage log base") |
| all ten others (`SSZ_INPUT_DECODED`, `EXECUTION_WITNESS_AREA`, `NODE_DB_BUCKETS`, `CODE_DB_BUCKETS`, `EVM_FRAME_STACK`, `EVM_VALUE_STACK`, `EVM_MEMORY_AREA`, `KECCAK/ECRECOVER/SHA256_SCRATCH`) | `0xa0…` | **0** |

Only `STATE_TRACKER_AREA` is wired into the current guest, and it uses a **2 MiB**
window `0xa0630000..0xa0830000` (16384×128 storage-log rows — confirmed by the
2 refs to `0xa0830000` and the `BlockVerdictParams` comment), not the 4 MiB slab
budgeted in `MemoryLayout.lean`. The current guest's actual EVM memory / stack /
opcode tables live in the linked `.data`, not the anchors:
`evm_memory@0xb796dac0`, `evm_stack_low@0xb8938040`, `lp64_stack@0xb88f7e40`,
`opcode_handlers@0xb8945270`.

This is **not a soundness bug** — `MemoryLayout.lean` states it is the contract
for the `Stateless/` port, which does not yet drive the emit. It IS a
doc/reality gap worth flagging: `guestRegionMap` (emitted reality) uses the one
live anchor's real 2 MiB window (`state_tracker_live`); the ten unused anchors
stay in the separate aspirational `schemeAAnchors` list. The current guest's
actual EVM memory / stack / opcode tables live in the linked `.data`, not the
anchors: `evm_memory@0xb796dac0`, `evm_stack_low@0xb8938040`,
`lp64_stack@0xb88f7e40`, `opcode_handlers@0xb8945270`.

### FINDING — two realities the section/anchor lists omit (added after review)

An independent scan for absolute `li` constants in `0xa0000000..0xa3000000` and
the sole `sp` init surfaced two regions neither scheme covered:

1. **The RV64 call stack.** `_start` executes `li sp, 0xa0050000`
   (`StatelessGuestEpilogue`, the only `sp` init in the image); the stack grows
   DOWN from `0xa0050000` — straight through the aspirational
   `execution_witness_area` slab `[0xa0030000, 0xa0130000)` and, if deeper than
   128 KiB, into `ssz_input_decoded`. This is the divergence the bead exists to
   surface: routine triples framed against the scheme-A anchors would be unsound
   w.r.t. the real guest. `MemoryLayout.lean`'s own table also omits the stack
   (upstream gap inherited). Modelled as `guest_stack` `[0xa0020000, 0xa0050000)`
   (192 KiB budget bottoming at OUTPUT's top; the guest has **no** explicit
   stack-depth guard, so this is a safe budget, not a proven max). The collision
   is kernel-checked: `guestStack_overlaps_executionWitnessArea` and
   `guestStack_not_disjoint_from_schemeA`. **A P1 divergence bead is filed** to
   reflow the scheme-A anchors clear of the stack before the port goes live; the
   collision was input to the phase-ownership half (now delivered — see the
status update at the top).
2. **ZisK system band.** The guest reads/writes `0xa0009828` (the ZisK MTVEC
   trap-vector slot, `StatelessGuestEpilogue` trap save/restore), inside
   `[0xa0000000, 0xa0010000)`, which no scheme covered. Modelled as `zisk_system`
   so the emitted-reality map accounts for every byte the guest touches.

---

## 2. Evidence per region size

**Emitted-reality map (`guestRegionMap`)** — what the current guest touches;
carries `guestRegionMap_pairwise_disjoint` (no exceptions):

| region | base | size | evidence | stability |
|---|---|---|---|---|
| INPUT | `0x40000000` | `0x2000` | `Programs INPUT_ADDR`; SSZ body at `+16` | STABLE |
| `zisk_system` | `0xa0000000` | `0x10000` | ZisK MTVEC slot `0xa0009828` | STABLE |
| OUTPUT | `0xa0010000` | `0x10000` | `Programs OUTPUT_ADDR` | STABLE |
| `guest_stack` | `0xa0020000` | `0x30000` | `_start li sp,0xa0050000` (grows down) | top STABLE; depth unguarded |
| `state_tracker_live` | `0xa0630000` | `0x200000` | emitted storage-log window `..0xa0830000` | STABLE |
| `.text` | `0x80000000` | `0x58150` | `readelf -S` | **LINK-DEPENDENT** |
| `.data` | `0xa3000000` | `0x15945a70` (ends `0xb8945a70`) | `readelf -S` | base STABLE, **size LINK-DEPENDENT** |
| `.sszscratch` | `0xbf500000` | `0x680000` | `readelf -S`; `MemoryLayout SSZ_SCRATCH_*` | STABLE |

**Aspirational scheme-A anchors (`schemeAAnchors`)** — the port contract; size =
gap to next anchor (reserved slab). `schemeA_matches_layout` pins each base to
the `Word` constant's `.toNat`. NOT part of the emitted map (collides with
`guest_stack`).

**Scheme A anchors** — size = the gap to the next anchor (the reserved slab), per
`MemoryLayout.lean`'s table. `RegionMap.schemeA_matches_layout` pins each base to
the corresponding `Word` constant's `.toNat`.

| region | base | size (slab) | evidence |
|---|---|---|---|
| `ssz_input_decoded` | `0xa0020000` | 64 KiB | anchor gap |
| `execution_witness_area` | `0xa0030000` | 1 MiB | anchor gap |
| `node_db_buckets` | `0xa0130000` | 4 MiB | anchor gap |
| `code_db_buckets` | `0xa0530000` | 1 MiB | anchor gap |
| `state_tracker_area` | `0xa0630000` | 4 MiB slab / **2 MiB live** | emitted guest storage log `..0xa0830000` |
| `evm_frame_stack` | `0xa0a30000` | 256 KiB | anchor gap |
| `evm_value_stack` | `0xa0a70000` | 1 MiB | anchor gap |
| `evm_memory_area` | `0xa0b70000` | 16 MiB | anchor gap |
| `keccak_scratch` | `0xa1b70000` | 64 KiB | anchor gap |
| `ecrecover_scratch` | `0xa1b80000` | 64 KiB | anchor gap |
| `sha256_scratch` | `0xa1b90000` | 64 KiB | anchor gap |

`state_tracker_area` (aspirational, 4 MiB slab) vs `state_tracker_live` (emitted,
2 MiB used) is the same base `0xa0630000` at two extents; the emitted-reality map
uses the live 2 MiB. `.text`/`.data` **sizes** are ELF ground truth (`readelf -S`)
and move whenever any function or data object changes
size; `RegionMap.textSizeBytes`/`dataSizeBytes` record the current ELF values and
`check-region-map.sh` re-derives them (regenerate on drift — see §5).

The top RW `LOAD` segment ends at `.data` end `0xb8945a70`, comfortably below the
`0xc0000000` ziskemu RAM ceiling (`readelf -lW`; checked structurally).

---

## 3. Overlap inventory (the `call_frame_arena` union) — the ONLY aliasing

The guest has exactly one intentional physical overlap. `call_frame_arena`
(~228 MiB EVM call-frame overlay, `frameArrayBytes = 1025 × 0x39000`) coalesces
**seven** execution-dead Phase-H arenas into its front. ELF ground truth
(`readelf -s`, this build) — all offsets confirmed by `check-region-map.sh`:

| symbol | address | arena-relative offset | size |
|---|---|---|---|
| `call_frame_arena` == `basr_values` | `0xac44d520` | `0` | `S` = 25,604,608 |
| `basr_accounts` | `0xadcb8720` | `S` | `S` |
| `bv_system_storage_log` | `0xaf523920` | `2S` | `L` = 76,800,000 |
| `baap_storage_desc` | `0xb3e61920` | `2S+L` | 4,000,000 |
| `baap_storage_paths` | `0xb4232220` | `2S+L+desc` | 6,400,000 |
| `baap_storage_delete_paths` | `0xb484ca20` | `+path` | 6,400,000 |
| `baap_storage_values` | `0xb4e67220` | `+2·path` | 6,400,000 |
| `call_frame_arena_end` | `0xb6876520` | `frameArrayBytes` | — |

where `S = bsrMaxStateChanges·bsrEncodedAccountBytes`,
`L = bvSystemStorageLogBytes` (`BlockVerdictParams.lean`).

Machine-checked in `RegionMap.lean`:

- `aliasedPairs` — the exhaustive list of overlapping pairs, each
  `(call_frame_arena, <child>)`; `aliasedPairs_shape` fixes it to exactly the
  seven above.
- `aliasedPairs_overlap_ranges` — the precise overlap RANGE (arena-relative
  `[off, off+size)`) of every aliased pair, as a machine-checked table.
- `dataUnionChildren_pairwise_disjoint` — the seven children own **mutually
  disjoint** sub-ranges (no self-corruption *among the coalesced arenas*).
- `dataUnionChildren_fit_arena` + `callFrameArena_within_data` — the union stays
  inside `call_frame_arena`, which stays inside `.data`.

These reproduce, at the region-map level, the fit gates already in
`CallFrameLayout.lean` (`frameArray_unions_basr_syslog_baap`), now anchored to
the actual ELF addresses.

**Design note (judgment call).** `guestRegionMap` is kept at *section/anchor*
granularity, where it is genuinely disjoint with **no** exception list — the one
aliasing lives entirely inside the single `.data` member and is expanded as its
own inventory (`dataUnionChildren`/`aliasedPairs`). This is cleaner than folding
the union arenas into `guestRegionMap` and carrying a mixed containment+aliasing
exception list, and keeps the soundness-relevant overlap set (the seven pairs)
unmuddied. `callFrameArena_within_data` composes the two views.

---

## 4. What the phase-ownership proof establishes (DELIVERED — kept for the record)

The overlaps above are documented, **not** proven safe. The current safety
argument (`CallFrameLayout.lean:99-120`, `docs/call-frame-memory-layout.md` §5)
is a prose phase-liveness claim: the seven coalesced arenas are **Phase-H**
scratch (built and consumed entirely within the pre-dispatch `block_state_root`
recompute — `BalAccountStateRoot`/`BlockVerdictStateRoot`/`BalAccountApplyPostFields`/
`BlockVerdictSysChange`), while `call_frame_arena` is **Phase-D** scratch
(referenced only by `CallFrameBase`/`Descend`/`Return` during dispatch). The
phases run sequentially with disjoint live windows, so time-sharing the bytes is
claimed sound.

The hard half (bead `.6`, delivered in #9724 + audited in #9851) turned that
prose into a verified
separation-logic / phase-ownership model:

1. A formal notion of the two live windows (Phase-H state-root recompute vs
   Phase-D dispatch) over the guest's control flow.
2. A proof that no Phase-D reader/writer of `call_frame_arena` is reachable while
   any of the seven arenas is live, and vice versa (the `#8513` execution-dead
   gate, made kernel-checked instead of a grep).
3. A guard that any future post-`block_state_root` read of the seven arenas
   breaks the model loudly (the union is otherwise a silent corruption vector).

This overlap inventory (`aliasedPairs` + the `_overlap` theorems + the mutual
disjointness of the children) is that proof's input: it fixes *which* bytes are
shared and *over what ranges*, leaving only the temporal-exclusion argument.

> **STATUS — DELIVERED.** The phase-ownership model landed as
> `EvmAsm/Rv64/SAsm/PhaseSplit.lean` (generic havoc'd-ownership machinery:
> `anyBytes`, tiling equalities, `cpsTripleWithin_anyBytes_pre`) +
> `EvmAsm/Codegen/CallFramePhase.lean` (the union instantiation:
> `phaseD_eq_phaseH`, `phaseHView_children`, `phaseH_to_phaseD`). Design
> write-up: `docs/sasm-design.md` §3.9. Items 1–3 above are realized as an
> *ownership* discipline rather than a control-flow analysis: the arena is
> ONE resource; exactly one phase's tiling of it exists in the ambient at
> any point of the composed proof; transitions forget contents by
> construction, so a stale reader receives havoc'd buffers (item 3's "loud
> break" = its triple becomes unprovable for want of the child view).
> Item 2's temporal claim is discharged per-routine as the `.41`–`.48` /
> `.49`/`.56` triples land and `.61` composes them — the model makes the
> unsound interleavings unexpressible rather than proving the current
> binary avoids them.

---

## 5. Drift handling

The scalar journal initialization obligations that feed the next predicate
layer are recorded in
[`docs/4ch8f-dispatch-journal-initialization.md`](4ch8f-dispatch-journal-initialization.md).
That document is cell/lifetime vocabulary, not another absolute-address map:
the twelve zero-assuming readers are load-bearing, while the two sampled
no-write cells remain retained until an all-path proof exists.

`scripts/check-region-map.sh` skips gracefully when the RISC-V toolchain is
absent (exit 0). Otherwise it hard-fails on:

- **structural drift** (section bases, RAM ceiling, `.data < .sszscratch`, and
  every union-placement fact) — these must never change silently;
- **link-layout drift** (`.text`/`.data` sizes vs `RegionMap.textSizeBytes`/
  `dataSizeBytes`, and the `symbol-addresses.tsv` snapshot).

Fix link-layout drift after any guest change:

```
scripts/gen-symbol-addresses.py --build      # regenerate the .9.3 TSV snapshot
# then update RegionMap.textSizeBytes / dataSizeBytes to the reported ELF sizes
```

This keeps the Lean map matching the ELF (the `.6` contract) instead of quietly
diverging.

For the **full** regen procedure covering all four generated files
(`symbol-addresses.tsv`, `GuestAddrs.lean`, `RegionMap.lean` sizes, and
`GuestImageEntries.lean`) in order, see
[`docs/regenerating-generated-files.md`](regenerating-generated-files.md).

---

## 6. The `.9.3` linker-facts table

`scripts/asm-fixtures/symbol-addresses.tsv` (generated by
`scripts/gen-symbol-addresses.py`) maps every defined symbol in the linked
`stateless_guest` ELF to its address, section, and a **STABLE vs LINK_DEPENDENT**
classification. Wave `.9.3` (550 functions using `la`/cross-function `jal`) needs
this distinction:

- **STABLE** (5 rows: the section bases; plus the INPUT/OUTPUT constants and the
  scheme-A anchors mirrored in `RegionMap.stableGuestBases`) — pinned by codegen
  constants / linker flags; may be hardcoded by `la` consumers.
- **LINK_DEPENDENT** (all ~2,789 emitted symbols — 801 `.text` function entries,
  ~1,977 `.data` arena/label addresses) — move on any `.text`/`.data` size
  change; `.9.3` must resolve them from the ELF at build time, never bake them
  into Lean.

The `runtime_dispatcher` unit is **not** independently linkable (it has undefined
cross-unit references); it and the ~873 `*Function` routines are spliced into
`stateless_guest`, so every entry the wave needs is a symbol in that one ELF. The
`la`-vs-`AUIPC+ADDI` encoding question stays with `.9.3`.
