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

/-- EVM memory per frame is no longer carried IN the frame slot: nested-frame
    memory is decoupled into the shared `evm_memory_pool` (evm-asm-274cr,
    `docs/evm-memory-pool-plan.md`) so a frame can use its full affordable
    ~2.90 MiB while the live total stays under the pool. The slot therefore
    holds NO memory sub-region (`frameMemBytes = 0`); the pool is a LIFO stack
    (`child_membase = parent_membase + ceil32(parent MSIZE)`). Kept as a named
    `0` so the derived sub-offset chain / `frameSegs` shape below is unchanged
    (the memory segment is empty). -/
def frameMemBytes : Nat := 0

/-- Shared EVM-memory pool for nested (depth ≥ 1) frames: 96 MiB. Replaces the
    former 1025 × 128 KiB per-slot reservations. Sized above the joint
    total-live bound (~70 MiB — all live frames share one tx's
    `TX_MAX_GAS_LIMIT = 2^24` regular gas; see `docs/memory-arena-gas-bound.md`),
    so a valid block never overflows and any overflow is a legitimately-invalid
    (>2^24 regular gas) block. Net vs the old per-slot reservation: −33 MiB
    (reclaim 128, add 96). -/
def evmMemoryPoolBytes : Nat := 0x6000000

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

/-- Per-frame stride: `frameUsedBytes` (`0x18800`, memory decoupled to the pool)
    rounded up to the 4 KiB-aligned `0x19000` (100 KiB). Frame `d` lives at
    `frameArrayBase + d * frameStride`. This is the **ground-truth** stride the
    emitted runtime uses: `frame_base` steps by `0x19000` (`LUI x6, 25` in
    `CallFrameBase.lean`) and the arena `.zero` pad is sized from
    `frameArrayBytes` below, so the two can no longer diverge. Shrunk from
    `0x39000` when the 128 KiB memory sub-region left the slot (evm-asm-274cr). -/
def frameStride : Nat := 0x19000

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

-- `frame_base` steps by `0x19000` (`LUI x6, 25`, `CallFrameBase.lean`).
#guard frameStride = 0x19000
-- `call_frame_descend`/`_return` set the child stack top at `+0x8200`.
#guard frameStackTopOff = 0x8200
-- `call_frame_descend`/`_return` set the child env base at `+0x18400`.
#guard frameEnvOff = 0x18400
-- Memory is decoupled to `evm_memory_pool`; the slot holds no memory sub-region.
#guard frameMemBytes = 0
-- Pool covers the joint total-live bound (~70 MiB; see the pool plan) with margin.
#guard evmMemoryPoolBytes ≥ 0x4800000

/-! ## Depth bound (execution-specs `STACK_DEPTH_LIMIT`) -/

/-- EVM stack-depth limit: a call from depth `d` is rejected when
    `d + 1 > maxCallDepth` (`vm/instructions/system.py:116`), so the deepest
    *executing* frame is depth `maxCallDepth`. -/
def maxCallDepth : Nat := 1024

/-- Frame slots needed: depths `0 .. maxCallDepth` inclusive ⇒ 1025. -/
def frameSlotCount : Nat := maxCallDepth + 1

/-! ## Guest memory map (matches `EvmAsm/Codegen/Driver.lean` ld flags) -/

/-- `-Tdata=` base. -/
def dataBase : Nat := 0xa0b00000
/-- `--section-start=.sszscratch=` base. -/
def sszScratchBase : Nat := 0xbf980000

/-- Total bytes the pre-allocated frame array occupies. -/
def frameArrayBytes : Nat := frameSlotCount * frameStride

/-! ## Placement: the frame arena coalesces five BAL-replay children

    ziskemu's RAM is 512 MiB (`0xa0000000..0xc0000000`). The current Amsterdam
    200M layout (`bsrMaxBalItems = 100000`) coalesces the execution-dead
    `basr_values`/`basr_accounts` pair and the three `baap_storage_*` arrays
    into the front of `call_frame_arena`. The current frame array is
    `1025 * 0x19000 = 104,960,000 B` (about 100.1 MiB), larger than the
    coalesced child prefix (about 61.6 MiB), with a trailing pad. The retired
    storage-log probe arenas are not part of the linked guest image;
    `evm_memory_pool` follows the frame arena.

    The historical 1G layout used a 244 MiB basr union and a 228 MiB frame
    stride. Those values remain useful in the design history but are not live
    geometry. The current phase-ownership argument is the same execution-dead
    Phase-H / Phase-D sequencing: the five child arrays are used during the
    pre-dispatch state-root recompute, while the frame arena is used during
    dispatch. See `docs/call-frame-memory-layout.md` §5. -/

/-- Total bytes of all 200M-sized BAL/state-replay static arenas
    (`bsr_changes` + `basr_records/paths/values/accounts` +
    `baap_storage_desc/paths/values`), matching the `.zero`
    declarations in `BlockVerdictDataSection.lean`. -/
def balArenaTotalBytes : Nat :=
  bsrMaxStateChanges * bsrStateChangeBytes
    + bsrMaxStateChanges * bsrAccountRecordBytes
    + bsrMaxStateChanges * bsrPathBytes
    + 2 * (bsrMaxStateChanges * bsrEncodedAccountBytes)
    + bsrMaxBalItems * baapStorageDescBytes
    + 2 * (bsrMaxBalItems * bsrPathBytes)

/-! ## Verified consistency invariants (kernel-checked `decide`) -/

/-- The stride is 32-aligned (the project avoids misaligned load/store). -/
theorem frameStride_aligned : frameStride % 32 = 0 := by decide

/-- All sub-regions fit within one stride (with slack rounding up to `frameStride`). -/
theorem frameUsed_fits_stride : frameUsedBytes ≤ frameStride := by decide

/-- Sub-region offsets are strictly increasing and the last ends within stride. -/
theorem frameMeta_within_stride : frameMetaOff + frameMetaBytes ≤ frameStride := by
  decide

/-- 1025 slots cover depths 0..1024 inclusive. -/
theorem frameSlotCount_eq : frameSlotCount = 1025 := by decide

/-- **Overrun closed (load-bearing):** the deepest reachable frame is depth
    `maxCallDepth` (1024), and the current emitted `frame_base(d)` uses
    `d * frameStride` with `frameStride = 0x19000`. The slot at depth 1024
    therefore ends at `maxCallDepth * frameStride`, which is inside the
    `frameArrayBytes = frameSlotCount * frameStride` arena. The old geometry
    divergence is historical; this guard pins the current 1025-slot geometry
    rather than carrying either old `0x29000` or `0x39000` as a live value. -/
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

/-- **Union-fits gate (load-bearing), post-`4ch8f.73`:** the basr pair + the three
    Phase-H `baap_storage_*` arenas (`baap_storage_desc` + the `baap_storage_paths` and `baap_storage_values` arrays)
    all fit within the frame array, so the five coalesced foreign arenas
    occupy distinct, non-overlapping, 32-aligned sub-ranges at the front of
    `call_frame_arena` (`[0,S)`, `[S,2S)`, then baap at `[2S, …)`) with a
    non-negative trailing pad to `frameArrayBytes`. All five are Phase-H
    (state-root recompute) scratch, dead during the Phase-D dispatch window when
    the frame array is live. The retired storage-log probe arenas are not among
    them. Replaces the former
    `frameArray_unions_basr_and_syslog` / `frameArray_unions_basr_syslog_baap`. -/
theorem frameArray_unions_basr_baap :
    2 * (bsrMaxStateChanges * bsrEncodedAccountBytes)
      + bsrMaxBalItems * baapStorageDescBytes + 2 * (bsrMaxBalItems * bsrPathBytes)
      ≤ frameArrayBytes := by decide

/-- **The fits proof that actually matters (200M layout):** the BAL/state-replay
    arenas (~83 MiB at the 200M capacity) plus the standalone 1025-slot frame
    array (104,960,000 B, about 100.1 MiB at the current `0x19000` stride) stay well inside
    the `.data`→`.sszscratch` span
    (GH #11186: `0xa0b00000`→`0xbf980000` = 518.5 MiB). The ELF-level ground
    truth is `readelf -lW`: the top RW LOAD address must stay below the
    0xc0000000 RAM ceiling. (Replaces `frameArray_fits_union`, which pinned the
    retired #8513 basr aliasing.) -/
theorem frameArray_and_balArenas_fit :
    balArenaTotalBytes + frameArrayBytes ≤ sszScratchBase - dataBase := by decide

/-- The usable `.data`→`.sszscratch` span is `0x1ee80000` = 518,520,832 B
    = 494.5 MiB (GH #11186: dataBase dropped to `0xa0b00000`). Under the 200M
    layout the BAL-replay arenas (~83 MiB) and the current standalone frame
    array (104,960,000 B, about 100.1 MiB) leave ample room for the rest. -/
theorem data_gap_bytes : sszScratchBase - dataBase = 0x1ee80000 := by decide

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
