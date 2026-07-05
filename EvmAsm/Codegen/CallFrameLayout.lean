/-
  EvmAsm.Codegen.CallFrameLayout

  Verified constants for the depth-indexed pre-allocated nested call-frame
  memory layout (EVM CALL/CREATE nesting up to the protocol depth limit).

  See `docs/call-frame-memory-layout.md` (design, bead `fhsxz.2.4.2.61.2`).
  This module is the machine-checked foundation for the layout
  implementation (bead `fhsxz.2.4.2.61.3`): every size/offset/placement
  figure the design asserts in prose is pinned here as a `def` and the
  consistency conditions (alignment, sub-regions fit the stride, the whole
  array fits the `.data`→`.sszscratch` gap) are proved with the kernel-checked
  `decide` (no `native_decide`/`bv_decide`).

  The constants are emitted into the guest by a later slice; defining them here
  first lets the address-map arithmetic be verified independently of the asm
  emit, so a units slip (e.g. MiB vs MB) cannot reach `.data`.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

/-! ## Per-frame sub-region sizes (bytes) -/

/-- EVM memory arena per frame: 128 KiB. **Canonical source** for the per-frame
    EVM memory capacity — `Dispatch.runtimeMemoryBytes` (the depth-0 global
    `evm_memory`) derives from this, and the `call_frame_descend` zero-loop clears
    exactly this many bytes of each slot on entry (`CallFrameDescend.lean:50-62`,
    `li t0, 0x20000`). Grown from 64 KiB to cover large runtime LOG/COPY ranges;
    the arena stride/size below follow. -/
def frameMemBytes : Nat := 0x20000

/-- Operand-stack guard band (one on each side of the stack arena). -/
def frameStackGuardBytes : Nat := 512

/-- EVM operand stack: 1024 words × 32 B = 32 KiB (protocol stack depth). -/
def frameStackBytes : Nat := 0x8000

/-- Per-frame returndata buffer: the last sub-call's output, copied in on
    return because the child slot is reused by the parent's next call. -/
def frameReturndataBytes : Nat := 0x10000

/-- Per-frame env subblock (ADDRESS/SELFBALANCE/CALLER/CALLVALUE, calldata
    ptr/len, log checkpoints, codeSize, isStatic, gasRemaining); 768 B. -/
def frameEnvBytes : Nat := 0x300

/-- Saved PC (x10) cell. -/
def framePcBytes : Nat := 8

/-- Saved code base (x21 → witness.codes slice) cell. -/
def frameCodebaseBytes : Nat := 8

/-- Frame metadata: caller depth, return offset/len into parent memory,
    is_static / is_create flags, created address, state-checkpoint id. -/
def frameMetaBytes : Nat := 0xF0

/-- Total bytes a single frame's sub-regions occupy (memory + both stack
    guards + stack + returndata + env + pc + codebase + meta). -/
def frameUsedBytes : Nat :=
  frameMemBytes + frameStackGuardBytes + frameStackBytes + frameStackGuardBytes
    + frameReturndataBytes + frameEnvBytes + framePcBytes + frameCodebaseBytes
    + frameMetaBytes

/-- Per-frame stride: `frameUsedBytes` (`0x38800`) rounded up to the 32-aligned
    (in fact 4 KiB-aligned) `0x39000` (228 KiB). Frame `d` lives at
    `frameArrayBase + d * frameStride`. This is the **ground-truth** stride the
    emitted runtime uses: `frame_base` steps by `0x39000` (`LUI x6, 57` in
    `CallFrameBase.lean:36`) and the arena `.zero` pad is sized from
    `frameArrayBytes` below, so the two can no longer diverge. -/
def frameStride : Nat := 0x39000

/-! ## Sub-region offsets within a frame slot (bytes from the slot base) -/

def frameMemOff : Nat := 0
def frameStackGuardLoOff : Nat := frameMemOff + frameMemBytes
def frameStackLowOff : Nat := frameStackGuardLoOff + frameStackGuardBytes
/-- `x12` init: stack grows *down* from the top of the stack arena. -/
def frameStackTopOff : Nat := frameStackLowOff + frameStackBytes
def frameStackGuardHiOff : Nat := frameStackTopOff
def frameReturndataOff : Nat := frameStackGuardHiOff + frameStackGuardBytes
def frameEnvOff : Nat := frameReturndataOff + frameReturndataBytes
def framePcOff : Nat := frameEnvOff + frameEnvBytes
def frameCodebaseOff : Nat := framePcOff + framePcBytes
def frameMetaOff : Nat := frameCodebaseOff + frameCodebaseBytes

/-! ## Drift pins: model geometry ≡ emitted literals (kernel-checked `#guard`)

    The emitted runtime hardcodes these figures in the frame-addressing asm
    (`CallFrameBase`/`CallFrameDescend`/`CallFrameReturn`); the arena `.zero`
    size derives from `frameArrayBytes` (this module). Pinning the model offsets
    to the emitted immediates here means a change to any per-frame sub-region size
    fails loudly instead of silently under-sizing the arena (the `.71`
    stride/arena divergence that this reconciliation closes). -/

-- `frame_base` steps by `0x39000` (`LUI x6, 57`, `CallFrameBase.lean:36`).
#guard frameStride = 0x39000
-- `call_frame_descend`/`_return` set the child stack top at `+0x28200`
-- (`CallFrameDescend.lean:60`, `CallFrameReturn.lean:261`).
#guard frameStackTopOff = 0x28200
-- `call_frame_descend`/`_return` set the child env base at `+0x38400`
-- (`CallFrameDescend.lean:62`, `CallFrameReturn.lean:256`).
#guard frameEnvOff = 0x38400
-- The descend zero-loop clears `0x20000` per slot; `Dispatch.runtimeMemoryBytes`
-- is the same value (and derives from this def).
#guard frameMemBytes = 0x20000

/-! ## Depth bound (execution-specs `STACK_DEPTH_LIMIT`) -/

/-- EVM stack-depth limit: a call from depth `d` is rejected when
    `d + 1 > maxCallDepth` (`vm/instructions/system.py:116`), so the deepest
    *executing* frame is depth `maxCallDepth`. -/
def maxCallDepth : Nat := 1024

/-- Frame slots needed: depths `0 .. maxCallDepth` inclusive ⇒ 1025. -/
def frameSlotCount : Nat := maxCallDepth + 1

/-! ## Guest memory map (matches `EvmAsm/Codegen/Driver.lean` ld flags) -/

/-- `-Tdata=` base. -/
def dataBase : Nat := 0xa3000000
/-- `--section-start=.sszscratch=` base. -/
def sszScratchBase : Nat := 0xbf500000

/-- Total bytes the pre-allocated frame array occupies. -/
def frameArrayBytes : Nat := frameSlotCount * frameStride

/-! ## Placement: the frame arena UNIONS the BAL-replay basr pair (a1vvy, 200M)

    ziskemu's RAM is 512 MiB (`0xa0000000..0xc0000000`). Under the former
    1G-sized BAL arenas (`bsrMaxBalItems = 500000`, ~416 MiB) there was no free
    window, so the frame arena *aliased* the contiguous, execution-dead
    `basr_values`+`basr_accounts` pair (the #8513 union, 244 MiB ≥ 164 MiB).
    The Amsterdam target is 200M block gas (`bsrMaxBalItems = 100000`), which
    shrinks the BAL arenas to ~83 MiB; the union was retired (standalone arena)
    while the BAL downsize left free RAM. The 200M log/receipt capacity lifts
    (`vv4hr.3.4.*`) have since consumed that slack (measured `.data` headroom
    fell to ~59 MiB), so a1vvy REINSTATES the union to reclaim ~49 MiB.

    The size relation flipped: the frame array (`frameArrayBytes` ~228 MiB at the
    reconciled `0x39000` stride) is now
    LARGER than the basr pair (~49 MiB), so the pair is coalesced into the FRONT
    of `call_frame_arena` (`BlockVerdictDataSection.lean`) rather than the arena
    aliasing into the pair. Soundness is the same execution-dead disjointness
    #8513 established and is now load-bearing again: `basr_values`/`basr_accounts`
    are referenced ONLY in `BalAccountStateRoot`/`BlockVerdictStateRoot` (Phase H,
    pre-dispatch state-root recompute) with no post-replay reader, while
    `call_frame_arena` is referenced ONLY by `CallFrameBase`/`Descend`/`Return`
    (Phase D dispatch) — sequential, disjoint live windows. See
    `docs/call-frame-memory-layout.md` §5. -/

/-- Total bytes of all 200M-sized BAL/state-replay static arenas
    (`bsr_changes` + `basr_records/paths/values/accounts` +
    `baap_storage_desc/paths/delete_paths/values`), matching the `.zero`
    declarations in `BlockVerdictDataSection.lean`. -/
def balArenaTotalBytes : Nat :=
  bsrMaxStateChanges * bsrStateChangeBytes
    + bsrMaxStateChanges * bsrAccountRecordBytes
    + bsrMaxStateChanges * bsrPathBytes
    + 2 * (bsrMaxStateChanges * bsrEncodedAccountBytes)
    + bsrMaxBalItems * baapStorageDescBytes
    + 3 * (bsrMaxBalItems * bsrPathBytes)

/-! ## Verified consistency invariants (kernel-checked `decide`) -/

/-- The stride is 32-aligned (the project avoids misaligned load/store). -/
theorem frameStride_aligned : frameStride % 32 = 0 := by decide

/-- All sub-regions fit within one stride (with slack rounding up to 0x29000). -/
theorem frameUsed_fits_stride : frameUsedBytes ≤ frameStride := by decide

/-- Sub-region offsets are strictly increasing and the last ends within stride. -/
theorem frameMeta_within_stride : frameMetaOff + frameMetaBytes ≤ frameStride := by
  decide

/-- 1025 slots cover depths 0..1024 inclusive. -/
theorem frameSlotCount_eq : frameSlotCount = 1025 := by decide

/-- **Overrun closed (the `.71` fix, load-bearing):** the deepest reachable frame
    is depth `maxCallDepth` (1024); the emitted `frame_base(d) = arena + (d-1)*stride`
    places its slot at arena offset `(maxCallDepth-1)*frameStride`, so the slot spans
    `[(maxCallDepth-1)*frameStride, maxCallDepth*frameStride)`. This slot end stays
    within `frameArrayBytes`, i.e. the entire depth-1024 frame (memory/stack/env/…)
    lands inside `call_frame_arena` and never overruns into the following `.data`.
    With the STALE `frameStride = 0x29000` the arena was sized `1025*0x29000` while
    `frame_base` stepped `0x39000`, so this failed for every depth ≥ ~738 — that
    failure WAS the bug. It now passes for all 1025 slots against the corrected
    `0x39000` stride/arena. -/
theorem frameArray_covers_all_depths :
    maxCallDepth * frameStride ≤ frameArrayBytes := by decide

/-- **a1vvy union-fits gate (load-bearing):** the coalesced `basr_values` +
    `basr_accounts` pair fits within the frame array, so placing both at the
    front of `call_frame_arena` (with a trailing pad to `frameArrayBytes`) keeps
    every frame slot inside the arena. The two basr arenas occupy distinct,
    non-overlapping sub-ranges `[0, S)` and `[S, 2S)` where
    `S = bsrMaxStateChanges * bsrEncodedAccountBytes`. Replaces the retired
    `frameArray_fits_union` (which had the size relation the other way). -/
theorem frameArray_unions_basr_pair :
    2 * (bsrMaxStateChanges * bsrEncodedAccountBytes) ≤ frameArrayBytes := by decide

/-- **Union-fits gate (load-bearing), post-`4ch8f.73`:** the basr pair + the four
    Phase-H `baap_storage_*` arenas (`baap_storage_desc` + 3 `* bsrPathBytes` path
    arenas) all fit within the frame array, so the six coalesced foreign arenas
    occupy distinct, non-overlapping, 32-aligned sub-ranges at the front of
    `call_frame_arena` (`[0,S)`, `[S,2S)`, then baap at `[2S, …)`) with a
    non-negative trailing pad to `frameArrayBytes`. All six are Phase-H
    (state-root recompute) scratch, dead during the Phase-D dispatch window when
    the frame array is live. `bv_system_storage_log` is NO LONGER among them: it
    is read post-dispatch (a frame slot would clobber it), so `4ch8f.73` moved it
    to its own standalone `.data` region, provably disjoint from every frame slot
    (`RegionMap.syslog_disjoint_from_frameArena`). Replaces the former
    `frameArray_unions_basr_and_syslog` / `frameArray_unions_basr_syslog_baap`. -/
theorem frameArray_unions_basr_baap :
    2 * (bsrMaxStateChanges * bsrEncodedAccountBytes)
      + bsrMaxBalItems * baapStorageDescBytes + 3 * (bsrMaxBalItems * bsrPathBytes)
      ≤ frameArrayBytes := by decide

/-- **The fits proof that actually matters (200M layout):** the BAL/state-replay
    arenas (~83 MiB at the 200M capacity) plus the standalone 1025-slot frame
    array (~228 MiB at the reconciled `0x39000` stride) together stay well inside
    the `.data`→`.sszscratch` span
    (453 MiB) — ~142 MiB of slack for the remaining `.data` objects (~80 MiB
    measured). The ELF-level ground truth is `readelf -lW`: the top RW LOAD
    address must stay below the 0xc0000000 RAM ceiling. (Replaces
    `frameArray_fits_union`, which pinned the retired #8513 basr aliasing.) -/
theorem frameArray_and_balArenas_fit :
    balArenaTotalBytes + frameArrayBytes ≤ sszScratchBase - dataBase := by decide

/-- The usable `.data`→`.sszscratch` span is `0x1c500000` = 475,004,928 B
    = 453 MiB. Under the 200M layout the BAL-replay arenas (~83 MiB) and the
    standalone frame array (~228 MiB) leave ample room for the rest of `.data`. -/
theorem data_gap_bytes : sszScratchBase - dataBase = 0x1c500000 := by decide

/-- **vv4hr.3.4.2 PACK:** the active block-log arena = packed descriptors
    (32 B/gas-unit) + the 24 B/log meta table (with the packed desc byte-offset)
    + the gas/8 data byte arena. -/
def packedBlockLogArenaBytes : Nat :=
  bvBlockLogDescBytes + bvBlockLogMetaBytes + bvBlockLogDataBytes

/-- **Reclaim gate (load-bearing):** packing the block-log descriptor arena
    (32 B/gas-unit vs the infeasible 256 B/log stride) frees at least 100 MiB of
    the `.data`→`.sszscratch` window (actual ~115.2 MiB: 170.1 MiB fixed → 54.9 MiB
    packed). Kernel-checked so the headroom claim cannot silently regress. -/
theorem packedBlockLog_reclaim :
    (bvBlockLogFullDescBytes + bvBlockLogFullMetaBytes + bvBlockLogFullDataBytes)
      - packedBlockLogArenaBytes ≥ 100 * 1024 * 1024 := by decide

/-- **Fits gate (sanity bound):** the BAL/state-replay arenas + the frame array +
    the PACKED block-log arena together stay inside the `.data`→`.sszscratch`
    span. (The block-log arena is its own standalone region, NOT part of the
    call_frame_arena union; the ELF link via `readelf -lW` is the full ground
    truth, but this kernel bound pins the three giants.) -/
theorem packedBlockLog_and_layout_fit :
    balArenaTotalBytes + frameArrayBytes + packedBlockLogArenaBytes
      ≤ sszScratchBase - dataBase := by decide

end EvmAsm.Codegen
