# Implementation plan: shared stack-pool for nested-frame EVM memory (evm-asm-274cr)

*Closes the beyond-dense memory-window false-reject class structurally by
making per-frame EVM memory flat again — replacing the 1025 fixed 128 KiB
per-slot memory reservations with one shared LIFO buffer. Byte-tied +
proof-bearing; a wrong literal aliases frames (soundness hazard), so this is
the exact old→new change-map to execute in ONE coordinated pass.*

## Why it fits (verified arithmetic)

- Remove the `0x20000` memory sub-region from each frame slot: stride
  `0x39000 → 0x19000`, `frameArrayBytes 228 → 100 MiB` (**reclaim 128 MiB**).
- Add `evm_memory_pool = 96 MiB` (`0x6000000`).
- **Net `.data` change = −33 MiB** (reclaim 128 − pool 96); with the existing
  ~12 MiB headroom, ~45 MiB slack. No squeeze.
- Correctness bound: all live frames share one tx's `TX_MAX_GAS_LIMIT = 2^24`
  regular gas; max total-live nested memory ≈ 70 MiB < 96 MiB pool → a valid
  block never overflows; a block that would has spent >2^24 regular gas ⇒
  invalid ⇒ pool OOG is correct. (See `docs/memory-arena-gas-bound.md`.)

## Mechanism

- Depth 0 keeps its own `evm_memory` region (unchanged). Depths ≥1 take memory
  from the pool as a LIFO stack: `child_membase = parent_membase +
  ceil32(parent_MSIZE)` at descend (depth-1 child at pool offset 0). MSIZE is
  a 32-multiple so bases stay 32-aligned. A returned frame's region (above the
  current frame) is reused on resume — pure stack discipline, no allocator.
- Memory is flat within each frame ⇒ every window op works raw ⇒ the whole
  beyond-dense class closes and the sparse store / m8pdu / #10234 sparse paths
  become dead code (clean up later).

## Change-map (execute together; guest does not re-link until all done)

### 1. `EvmAsm/Codegen/CallFrameLayout.lean`
- Drop `frameMemOff`/`frameMemBytes` from the slot chain; slot starts at the
  stack guard. New offsets (verified): `frameStackGuardLoOff=0`,
  `frameStackTopOff=0x8200` (was `0x28200`), `frameEnvOff=0x18400` (was
  `0x38400`), `framePcOff=0x18700`, `frameCodebaseOff=0x18708`,
  `frameMetaOff=0x18710`, `frameUsedBytes=0x18800` (was `0x38800`),
  `frameStride=0x19000` (was `0x39000`).
- `#guard` updates: `frameStride=0x19000`; `frameStackTopOff=0x8200`;
  `frameEnvOff=0x18400`; DELETE `frameMemBytes=0x20000` guard.
- Add `def evmMemoryPoolBytes : Nat := 0x6000000` + `#guard evmMemoryPoolBytes
  ≥ 0x4800000` (72 MiB ≥ the ~70 MiB joint bound) with the derivation comment.
- Re-check the union/disjointness `decide` guards (arena front still ≥ basr
  pair: 100 MiB ≥ 49 MiB ✓).

### 2. `EvmAsm/Codegen/RegionMap.lean`
- `frameArrayBytes` auto-shrinks (derived). Add `evm_memory_pool` GuestRegion
  (96 MiB) placed after the shrunk frame arena; add its disjointness/fit
  `#guard`s and the `_matches_*` pin. Re-pin `dataSizeBytes` after regen.

### 3. `EvmAsm/Codegen/Programs/CallFrameBase.lean`
- `frame_base` stride immediate `LUI x6, 57 → LUI x6, 25` (0x39000→0x19000).
- Re-pin `frameBase_spec` SAsm proof (the multiply-by-stride witness). **This
  is the one verified proof that must be re-proved — expected, per maintainer.**

### 4. `EvmAsm/Codegen/Programs/CallFrameDescend.lean` (`call_frame_enter` + descend)
- Child memory base: instead of `frame_base(d)+frameMemOff`, compute
  `child_membase = (d==1 ? evm_memory_pool : parent_membase) + ceil32(parent_MSIZE)`
  — i.e. depth-1 child at pool base, deeper stacked on the parent (parent
  MSIZE from parent env+488). Return that as `a0` (x13). Stack/env bases still
  from the slot but at the NEW offsets.
- Stack-top literal `0x28200 → 0x8200`; env literal `0x38400 → 0x18400`.
- DELETE the eager `li t0, 0x20000` memory zero-loop (memory now zeroed
  lazily on expansion — item 6).
- Save `child_membase` in `frame_parent_bases[d]` as today (restore already
  works via that table).

### 5. `EvmAsm/Codegen/Programs/CallFrameReturn.lean` (`frame_return`)
- Stack-top literal `0x28200 → 0x8200`; env literal `0x38400 → 0x18400`
  (the two `#guard`-pinned sites). Memory-base restore already reads
  `frame_parent_bases` → no change (it now points into the pool).

### 6. `EvmAsm/Codegen/Programs/EvmMemoryGas.lean`
- `memoryArenaLimitAsm`: return `pool_end − frame_base` (remaining pool) for
  depth ≥1 instead of the `0x20000` constant; keep depth-0 = the `evm_memory`
  root arena bound. Every window op's bail becomes pool-relative automatically.
- `updateActiveMemorySizeAsm`: on MSIZE growth (`old<new`), zero
  `[frame_base+old, frame_base+new)` — spec "expand with zeros", gas-paid.
  (Replaces the eager per-enter zero-init removed in item 4.)

### 7. `Dispatch.lean` / `BlockVerdictDataSection.lean`
- Frame arena `.zero` size ← new `frameArrayBytes`. Declare `evm_memory_pool:
  .zero 0x6000000`. No per-tx reset needed (lazy zero-on-expansion handles
  freshness; the pool bump pointer is re-derived per descend from MSIZE).

### 8. Retire (dead-code, follow-up PR — not required for correctness)
- sparse store + `sparse_window_read/write` + m8pdu tag scans + #10234 window
  sparse paths become unreachable (memoryArenaLimit never trips beyond pool).
  Leave in place first (harmless), delete in a separate cleanup PR.

## Validation
- Kernel `#guard`s pass (geometry + pool bound).
- Witness: a depth-≥1 frame that MSTOREs/RETURNs a window > 128 KiB (up to a
  few hundred KiB) — succeeds when affordable, reads back correct bytes
  (pre-change: OOG-burn). A nested chain confirming siblings/children don't
  alias (parent memory intact across a child call that also uses memory).
- `frameBase_spec` (+ any frame-geometry proofs) re-proved, classical-3.
- regen (`GuestAddrs`/tsv/`RegionMap`/`GuestImage`) + byte-tie; all
  `check-*.sh` clean; RegionMap net −33 MiB.
- Full-suite A/B: 0 regressions (the whole memory path is touched — the dense
  path must stay byte-equivalent in behavior); plus the `.13`/precompile
  fixtures stay green and any latent beyond-128 KiB nested cases now pass.

## Order of execution
1 (layout consts) → 3 (frame_base LUI + proof) → 4/5 (enter/descend/return
offsets + pool base) → 6 (limit + zero-on-expansion) → 7 (data sections) → 2
(RegionMap) → regen/gates → witness + full-suite A/B. Land as one PR (the
layout is atomic); the sparse retirement (8) is a separate cleanup PR.
