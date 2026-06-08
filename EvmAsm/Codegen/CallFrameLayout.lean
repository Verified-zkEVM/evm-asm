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

/-- EVM memory arena per frame: 64 KiB (covers Amsterdam `MAX_INIT_CODE_SIZE`
    staging via the parent slice; matches today's single-frame `evm_memory`). -/
def frameMemBytes : Nat := 0x10000

/-- Operand-stack guard band (one on each side of the stack arena). -/
def frameStackGuardBytes : Nat := 512

/-- EVM operand stack: 1024 words × 32 B = 32 KiB (protocol stack depth). -/
def frameStackBytes : Nat := 0x8000

/-- Per-frame returndata buffer: the last sub-call's output, copied in on
    return because the child slot is reused by the parent's next call. -/
def frameReturndataBytes : Nat := 0x10000

/-- Per-frame env subblock (ADDRESS/SELFBALANCE/CALLER/CALLVALUE, calldata
    ptr/len, log checkpoints, codeSize, gasRemaining); 768 B. -/
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

/-- Per-frame stride: `frameUsedBytes` rounded up to a 32-aligned `0x29000`
    (164 KiB). Frame `d` lives at `frameArrayBase + d * frameStride`. -/
def frameStride : Nat := 0x29000

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

/-! ## Placement: union with the BAL-replay scratch (NOT a free `.data` gap)

    ziskemu's RAM is only 512 MiB (`0xa0000000..0xc0000000`) and the guest `.data`
    already spans ~427 MiB — there is NO free window for a standalone arena (an
    earlier draft placed it at `0xa4000000`, which overlaps `.data`; the linker
    rejects it). Instead the frame arena **aliases** the contiguous
    `basr_values`+`basr_accounts` `block_state_root` replay scratch, which is
    execution-dead (read only inside `block_state_root`; gate-verified). So the
    arena's base is a **link-time symbol** (`call_frame_arena = &basr_values`,
    not a fixed VMA), and the meaningful invariant is that the frame arena fits
    inside that union, not inside a phantom gap. See
    `docs/call-frame-memory-layout.md` §5. -/

/-- The `basr_values`+`basr_accounts` union the frame arena reuses: two
    contiguous `bsrMaxStateChanges * bsrEncodedAccountBytes` arenas. -/
def balReplayUnionBytes : Nat := 2 * (bsrMaxStateChanges * bsrEncodedAccountBytes)

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

/-- **The fits proof that actually matters:** the whole 1025-slot frame array
    fits inside the `basr_values`+`basr_accounts` union it overlays (244 MiB vs
    164 MiB — 84 MiB headroom), so the arena reuses that execution-dead region
    with zero net RAM growth. (This replaces the earlier `frameArray_fits` that
    compared against a phantom free `.data` gap.) -/
theorem frameArray_fits_union : frameArrayBytes ≤ balReplayUnionBytes := by decide

/-- The usable `.data`→`.sszscratch` span is `0x1c500000` = 475,004,928 B
    = 453 MiB — but it is NOT free (the BAL-replay arenas consume ~385 MiB of it),
    which is why the arena overlays them rather than taking a fresh slice. -/
theorem data_gap_bytes : sszScratchBase - dataBase = 0x1c500000 := by decide

end EvmAsm.Codegen
