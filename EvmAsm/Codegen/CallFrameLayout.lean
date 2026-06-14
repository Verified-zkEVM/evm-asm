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

/-! ## Placement: standalone block after the BAL-replay arenas (200M layout)

    ziskemu's RAM is 512 MiB (`0xa0000000..0xc0000000`). Under the former
    1G-sized BAL arenas (`bsrMaxBalItems = 500000`, ~416 MiB) there was no free
    window, so the frame arena *aliased* the contiguous, execution-dead
    `basr_values`+`basr_accounts` pair (the #8513 union, 244 MiB ≥ 164 MiB).
    The Amsterdam target is 200M block gas (`bsrMaxBalItems = 100000`), which
    shrinks the BAL arenas to ~83 MiB — the basr pair (~49 MiB) can no longer
    host the frame array, and the freed ~333 MiB means it no longer needs to:
    `call_frame_arena` is a standalone pre-zeroed `.zero frameArrayBytes` block
    emitted right after `basr_accounts` (`BlockVerdictDataSection.lean`), and
    the execution-dead soundness gate on `basr_values`/`basr_accounts` is no
    longer load-bearing. See `docs/call-frame-memory-layout.md` §5. -/

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

/-- **The fits proof that actually matters (200M layout):** the BAL/state-replay
    arenas (~83 MiB at the 200M capacity) plus the standalone 1025-slot frame
    array (~164 MiB) together stay well inside the `.data`→`.sszscratch` span
    (453 MiB) — ~206 MiB of slack for the remaining `.data` objects (~80 MiB
    measured). The ELF-level ground truth is `readelf -lW`: the top RW LOAD
    address must stay below the 0xc0000000 RAM ceiling. (Replaces
    `frameArray_fits_union`, which pinned the retired #8513 basr aliasing.) -/
theorem frameArray_and_balArenas_fit :
    balArenaTotalBytes + frameArrayBytes ≤ sszScratchBase - dataBase := by decide

/-- The usable `.data`→`.sszscratch` span is `0x1c500000` = 475,004,928 B
    = 453 MiB. Under the 200M layout the BAL-replay arenas (~83 MiB) and the
    standalone frame array (~164 MiB) leave ample room for the rest of `.data`. -/
theorem data_gap_bytes : sszScratchBase - dataBase = 0x1c500000 := by decide

end EvmAsm.Codegen
