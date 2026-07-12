/-
  EvmAsm.Codegen.Programs.EvmMemoryGas

  Runtime active-memory high-water tracking and EVM memory-expansion gas
  (M31). Extracted from Programs/Evm.lean so the main opcode registry stays
  under the file-size guardrail.

  The high-water mark (in bytes, a multiple of 32) lives at
  `env + activeMemorySizeOff`; `MSIZE` reads it. Memory-expansion gas (per
  `execution-specs/.../vm/gas.py` `calculate_memory_gas_cost`) is
  `cost(w) = GAS_MEMORY·w + ⌊w²/512⌋` with `GAS_MEMORY = 3` and `w` = 32-byte
  words; an access that grows the mark from `old` to `new` words is charged
  `cost(new) − cost(old)` (each `cost` floored independently).
-/

namespace EvmAsm.Codegen

/-- Dispatcher env offset (bytes) of the runtime active-memory high-water
    mark. `MSIZE` reads it; memory handlers update it. (Mirrors
    `mcopyActiveMemorySizeOff` in `EvmMcopyGas.lean`.) -/
def activeMemorySizeOff : Nat := 488

/-- Runtime EVM memory arena size for nested call/create frames. This remains
    tied to the preallocated call-frame layout. -/
def runtimeMemoryArenaLimitBytes : Nat := 0x20000

/-- Runtime EVM memory arena size for the depth-0 frame. Four MiB covers every
    memory expansion affordable under Amsterdam's 16,777,216 regular-gas cap:
    the quadratic term alone exceeds the cap above roughly 2.9 MiB. Keeping a
    rounded margin avoids rejecting valid high-memory RETURN/CALL programs while
    leaving nested frame slots at their fixed 128 KiB capacity. -/
def rootRuntimeMemoryArenaLimitBytes : Nat := 0x400000

-- Frontier's large identity-precompile case expands a 1,000,000-byte CALL
-- input window before the child call itself fails for insufficient gas.
#guard 1000000 ≤ rootRuntimeMemoryArenaLimitBytes

/-- Sparse high-memory backing for 32-byte MSTORE/MLOAD windows that exceed the
    materialized per-frame arena. This preserves execution-specs memory-expansion
    gas/MSIZE behavior for high offsets without treating the guest's dense arena
    limit as an EVM OOG condition. Entries are append-only per dispatch; MLOAD
    scans backward so later writes shadow earlier ones. Depth epochs prevent
    stale entries from a reused child-frame slot from becoming visible to a
    later frame at the same depth. The stored payload is the EVM stack-word limb
    representation, which is exactly what a matching MLOAD reconstructs from the
    big-endian byte layout of MSTORE. -/
def sparseMemoryWordCapacity : Nat := 4096

/-- Byte capacity of the `evm_precompile_frame` returndata data window (`+16`).

    Must be ≥ the largest length any staging path can write at `+8`, so the
    full returndata is always staged and RETURNDATACOPY's
    `start + size ≤ retlen` guard alone keeps reads inside staged bytes
    (matching execution-specs, with no implementation cap and no reads of
    unstaged bytes). The bound is architectural: a child RETURN/REVERT is
    limited to `runtimeMemoryArenaLimitBytes` by `returnRevertMemoryGasAsm`,
    and the IDENTITY precompile echoes an input bounded by the caller's arena
    — up to `rootRuntimeMemoryArenaLimitBytes` when called from depth 0 —
    which dominates (MODEXP ≤ 1024, all other precompiles ≤ 256). -/
def precompileFrameReturndataCapBytes : Nat := rootRuntimeMemoryArenaLimitBytes

/-- Load the materialized memory-arena bound for the current frame into `limitReg`.
    Depth 0 uses the larger root arena; nested frames use the fixed call-frame
    layout bound. -/
def memoryArenaLimitAsm (tag limitReg : String) : String :=
  "  la " ++ limitReg ++ ", evm_call_depth\n" ++
  "  ld " ++ limitReg ++ ", 0(" ++ limitReg ++ ")\n" ++
  "  beqz " ++ limitReg ++ ", .Lmemlimit_root_" ++ tag ++ "\n" ++
  "  li " ++ limitReg ++ ", " ++ toString runtimeMemoryArenaLimitBytes ++ "\n" ++
  "  j .Lmemlimit_have_" ++ tag ++ "\n" ++
  ".Lmemlimit_root_" ++ tag ++ ":\n" ++
  "  li " ++ limitReg ++ ", " ++ toString rootRuntimeMemoryArenaLimitBytes ++ "\n" ++
  ".Lmemlimit_have_" ++ tag ++ ":\n"

/-- Inline asm that updates the runtime `MSIZE` high-water mark from one
    memory access `(offset, length)` (low u64 limbs) and — when
    `chargeGas` is true — charges the EVM memory-expansion gas for any
    growth against `env.gasRemaining` (`env+568`, the M30 cell).

    `chargeGas = false` is for callers that have already charged their own
    memory gas (MCOPY, via `mcopyDynamicGasAsm`) and only need the size
    bookkeeping; passing `true` would double-charge them.

    If `length = 0` the EVM never expands memory, so the whole block is
    skipped. If the access does not grow the mark (`current ≥ rounded`),
    no gas is charged. A `mulhu` guard sends `w ≥ 2^32` (≈128 GiB,
    astronomically expensive) straight to `.exit_outofgas` rather than
    letting `w²` wrap mod 2^64; gas underflow likewise routes there
    (`halt_kind = 6`).

    Register use: `offsetReg` and `roundedReg` are preserved across the
    block; `lengthReg` is preserved (so MCOPY can keep the copy length in
    it across two calls); `maskReg`, `currentReg`, and `gasTmpReg` are
    clobbered as scratch. -/
def updateActiveMemorySizeAsm
    (tag offsetReg lengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) : String :=
  "  beqz " ++ lengthReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  "  add " ++ roundedReg ++ ", " ++ offsetReg ++ ", " ++ lengthReg ++ "\n" ++
  "  addi " ++ roundedReg ++ ", " ++ roundedReg ++ ", 31\n" ++
  "  li " ++ maskReg ++ ", -32\n" ++
  "  and " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ maskReg ++ "\n" ++
  "  ld " ++ currentReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  "  bgeu " ++ currentReg ++ ", " ++ roundedReg ++ ", .Lmemsize_" ++ tag ++ "_done\n" ++
  (if chargeGas then
    -- M31 expansion gas: charge cost(new_words) − cost(old_words). Temps:
    -- maskReg = words; gasTmpReg = new_cost then delta; currentReg → old_cost.
    "  srli " ++ maskReg ++ ", " ++ roundedReg ++ ", 5\n" ++            -- M = new words
    "  mulhu " ++ gasTmpReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  bnez " ++ gasTmpReg ++ ", .exit_outofgas\n" ++                   -- w² ≥ 2^64 ⇒ OOG
    "  mul " ++ gasTmpReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  srli " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", 9\n" ++           -- T = ⌊nw²/512⌋
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ maskReg ++ "\n" ++ -- T = new_cost
    "  srli " ++ maskReg ++ ", " ++ currentReg ++ ", 5\n" ++            -- M = old words
    "  mul " ++ currentReg ++ ", " ++ maskReg ++ ", " ++ maskReg ++ "\n" ++
    "  srli " ++ currentReg ++ ", " ++ currentReg ++ ", 9\n" ++         -- C = ⌊ow²/512⌋
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++
    "  add " ++ currentReg ++ ", " ++ currentReg ++ ", " ++ maskReg ++ "\n" ++ -- C = old_cost
    "  sub " ++ gasTmpReg ++ ", " ++ gasTmpReg ++ ", " ++ currentReg ++ "\n" ++ -- T = delta
    "  ld " ++ maskReg ++ ", 568(x20)\n" ++                             -- M = gas remaining
    "  bltu " ++ maskReg ++ ", " ++ gasTmpReg ++ ", .exit_outofgas\n" ++
    "  sub " ++ maskReg ++ ", " ++ maskReg ++ ", " ++ gasTmpReg ++ "\n" ++
    "  sd " ++ maskReg ++ ", 568(x20)\n"
   else "") ++
  "  sd " ++ roundedReg ++ ", " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
  ".Lmemsize_" ++ tag ++ "_done:\n"

/-- OOG guard for a memory access whose length is a NONZERO constant
    (MLOAD/MSTORE = 32, MSTORE8 = 1). For such accesses the EVM always grows
    memory to `offset + length`, so an `offset` that does not fit in a u64 — or
    whose low limb `+ length` wraps — has a memory-expansion cost vastly beyond
    any block gas limit and exceptionally halts (`evm.gas_left = 0`). The low-
    limb-only memory-gas path (`updateActiveMemorySizeAsm`) would otherwise read
    a truncated/wrapped offset and charge trivial gas, under-counting gas_used.

    `offsetReg` already holds the low offset limb (loaded by the caller from
    `0(x12)`); this reads the three high limbs from `8/16/24(x12)` into
    `scratchReg` and routes any nonzero high limb — or a `low + length`
    wraparound — to `.exit_outofgas` (halt_kind 6). `offsetReg` is preserved;
    `scratchReg` is clobbered. Mirrors the high-limb guards already present in
    `returnRevertMemoryGasAsm` / `callMemoryExpansionGasAsm`. Sound: it can only
    turn a should-OOG access from a trivial charge into the correct OOG, so it
    never lowers gas_used (no false-accept). -/
def memConstOffsetOogGuardAsm
    (tag offsetReg scratchReg : String) (length : Nat) : String :=
  "  ld " ++ scratchReg ++ ", 8(x12)\n" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas\n" ++
  "  ld " ++ scratchReg ++ ", 16(x12)\n" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas\n" ++
  "  ld " ++ scratchReg ++ ", 24(x12)\n" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas\n" ++
  "  addi " ++ scratchReg ++ ", " ++ offsetReg ++ ", " ++ toString length ++ "\n" ++
  "  bltu " ++ scratchReg ++ ", " ++ offsetReg ++ ", .exit_outofgas\n" ++
  memoryArenaLimitAsm ("const_" ++ tag) "x6" ++
  "  bltu x6, " ++ scratchReg ++ ", .exit_outofgas\n"


/-- Constant-length memory guard that rejects non-u64 offsets and low-limb
    wraparound, but deliberately does not enforce the materialized dense arena
    bound. Sparse high-memory handlers use this before charging memory expansion
    and routing the actual load/store to sparse backing when the dense arena is
    too small. -/
def memConstOffsetWrapOogGuardAsm
    (_tag offsetReg scratchReg : String) (length : Nat) : String :=
  "  ld " ++ scratchReg ++ ", 8(x12)
" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas
" ++
  "  ld " ++ scratchReg ++ ", 16(x12)
" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas
" ++
  "  ld " ++ scratchReg ++ ", 24(x12)
" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas
" ++
  "  addi " ++ scratchReg ++ ", " ++ offsetReg ++ ", " ++ toString length ++ "
" ++
  "  bltu " ++ scratchReg ++ ", " ++ offsetReg ++ ", .exit_outofgas
"

/-- `updateActiveMemorySizeAsm` for sparse-capable constant accesses. It charges
    memory expansion and updates MSIZE exactly like the dense helper, but leaves
    the dense-arena bound to the caller so out-of-arena accesses can use sparse
    backing instead of becoming implementation-limit OOG. -/
def updateActiveMemorySizeConstSparseAsm
    (tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) (length : Nat) : String :=
  (if length == 0 then "" else memConstOffsetWrapOogGuardAsm tag offsetReg maskReg length) ++
  "  li " ++ tmpLengthReg ++ ", " ++ toString length ++ "
" ++
  updateActiveMemorySizeAsm tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg chargeGas

/-- Runtime memory arena guard for a dynamic memory range `(offset, length)`
    whose low u64 limbs are already loaded. Zero-length ranges are no-ops and
    need no bound. Nonzero ranges whose low-limb end wraps or exceeds the
    dispatcher's 64 KiB per-frame arena route to OOG before the byte-copy body
    can write past the mapped ziskemu RAM window. High-limb rejection remains
    the caller's responsibility because stack layouts differ by opcode. -/
def memDynamicArenaOogGuardAsm
    (tag offsetReg lengthReg endReg limitReg : String) : String :=
  "  beqz " ++ lengthReg ++ ", .Lmemarena_" ++ tag ++ "_done\n" ++
  "  add " ++ endReg ++ ", " ++ offsetReg ++ ", " ++ lengthReg ++ "\n" ++
  "  bltu " ++ endReg ++ ", " ++ offsetReg ++ ", .exit_outofgas\n" ++
  memoryArenaLimitAsm ("arena_" ++ tag) limitReg ++
  "  bltu " ++ limitReg ++ ", " ++ endReg ++ ", .exit_outofgas\n" ++
  ".Lmemarena_" ++ tag ++ "_done:\n"

/-- Reject COPY-family memory ranges that cannot be represented by the
    runtime's low-u64 `(destination, size)` registers. The full words remain on
    the EVM stack. A nonzero high size limb always means an enormous nonzero
    range and therefore OOG. Only after proving the full size is nonzero do we
    inspect the destination high limbs: EVM copy operations ignore every
    destination bit for a genuinely zero-size range. -/
def memDynamicU256RangeOogGuardAsm
    (tag baseReg lengthReg scratchReg tmpReg : String)
    (destinationOff sizeOff : Nat) : String :=
  "  ld " ++ scratchReg ++ ", " ++ toString (sizeOff + 8) ++ "(" ++ baseReg ++ ")\n" ++
  "  ld " ++ tmpReg ++ ", " ++ toString (sizeOff + 16) ++ "(" ++ baseReg ++ ")\n" ++
  "  or " ++ scratchReg ++ ", " ++ scratchReg ++ ", " ++ tmpReg ++ "\n" ++
  "  ld " ++ tmpReg ++ ", " ++ toString (sizeOff + 24) ++ "(" ++ baseReg ++ ")\n" ++
  "  or " ++ scratchReg ++ ", " ++ scratchReg ++ ", " ++ tmpReg ++ "\n" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas\n" ++
  "  beqz " ++ lengthReg ++ ", .Lmemu256_" ++ tag ++ "_done\n" ++
  "  ld " ++ scratchReg ++ ", " ++ toString (destinationOff + 8) ++ "(" ++ baseReg ++ ")\n" ++
  "  ld " ++ tmpReg ++ ", " ++ toString (destinationOff + 16) ++ "(" ++ baseReg ++ ")\n" ++
  "  or " ++ scratchReg ++ ", " ++ scratchReg ++ ", " ++ tmpReg ++ "\n" ++
  "  ld " ++ tmpReg ++ ", " ++ toString (destinationOff + 24) ++ "(" ++ baseReg ++ ")\n" ++
  "  or " ++ scratchReg ++ ", " ++ scratchReg ++ ", " ++ tmpReg ++ "\n" ++
  "  bnez " ++ scratchReg ++ ", .exit_outofgas\n" ++
  ".Lmemu256_" ++ tag ++ "_done:\n"

/-- `updateActiveMemorySizeAsm` for a constant access length (MLOAD/MSTORE =
    32, MSTORE8 = 1). Materializes the length into `tmpLengthReg` first.

    For a nonzero `length` it FIRST emits `memConstOffsetOogGuardAsm`, so a
    256-bit offset that cannot be represented in a u64 (or whose low limb wraps
    when the length is added) exceptionally halts instead of charging trivial
    truncated-offset gas. `offsetReg` must already hold the low offset limb and
    the full 256-bit offset must live at `0(x12)` (as for MLOAD/MSTORE/MSTORE8).
    `maskReg` doubles as the guard scratch (it is clobbered by the size helper
    anyway). -/
def updateActiveMemorySizeConstAsm
    (tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) (length : Nat) : String :=
  (if length == 0 then "" else memConstOffsetOogGuardAsm tag offsetReg maskReg length) ++
  "  li " ++ tmpLengthReg ++ ", " ++ toString length ++ "\n" ++
  updateActiveMemorySizeAsm tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg chargeGas

/-- COPY-family dynamic word gas. The dispatch loop already charges each
    opcode's static base cost; this charges only
    `3 * ceil32(length) / 32` against `env.gasRemaining`.

    This helper preserves `lengthReg`, so callers can load the size once and
    then call `updateActiveMemorySizeAsm` for the destination range. It treats
    low-limb `length + 31` wraparound as OOG, matching memory-expansion style
    failures for ranges too large for this u64-addressed runtime. -/
def copyWordGasAsm (tag lengthReg roundedReg wordsReg gasReg : String) : String :=
  "  beqz " ++ lengthReg ++ ", .Lcopygas_" ++ tag ++ "_done\n" ++
  "  addi " ++ roundedReg ++ ", " ++ lengthReg ++ ", 31\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ lengthReg ++ ", .exit_outofgas\n" ++
  "  srli " ++ wordsReg ++ ", " ++ roundedReg ++ ", 5\n" ++
  "  slli " ++ gasReg ++ ", " ++ wordsReg ++ ", 1\n" ++
  "  add " ++ gasReg ++ ", " ++ gasReg ++ ", " ++ wordsReg ++ "\n" ++
  "  ld " ++ roundedReg ++ ", 568(x20)\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ gasReg ++ ", .exit_outofgas\n" ++
  "  sub " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ gasReg ++ "\n" ++
  "  sd " ++ roundedReg ++ ", 568(x20)\n" ++
  ".Lcopygas_" ++ tag ++ "_done:\n"

/-- RETURN/REVERT memory expansion gas. The opcode static cost is zero, so
    this charges only memory expansion over `(offset, size)` before the
    terminating data copy. Zero-size ranges do not expand memory, matching
    execution-specs. Nonzero ranges with high offset/size limbs, low-limb
    wraparound, or an end past the current materialized runtime memory arena route
    to `.exit_outofgas` before any return/revert output is emitted.

    Stack layout before RETURN/REVERT body: `offset` at `0(x12)`, `size` at
    `32(x12)`. Scratch registers x14/x15/x16/x17/x18/x19/x6 are clobbered.

    `sparseWindows = true` (call-frame guest only, evm-asm-0w05f.13): a
    depth-1+ CALL frame's window is valid iff its quadratic expansion gas is
    affordable, independent of the dense arena — `updateActiveMemorySizeAsm`
    charges the exact spec delta and the tail materializes the beyond-dense
    bytes from the sparse word store (`sparse_window_read`). The depth-0 root
    guard is preserved verbatim, and a CREATE child frame
    (`create_frame_flag[depth] = 1`) keeps the conservative dense bail: its
    RETURN deposits code via a raw `x13+offset` read (no sparse
    materialization), so out-of-arena initcode windows must still burn.
    `sparseWindows = false` keeps the original arena bail byte-identical
    (standalone probes; no `create_frame_flag` symbol dependency). -/
def returnRevertMemoryGasAsm (tag : String) (sparseWindows : Bool := false) : String :=
  -- Any non-zero high size limb means size is non-zero but not representable.
  "  ld x18, 40(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x18, 48(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x18, 56(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x15, 32(x12)\n" ++
  "  beqz x15, .Lreturn_revert_mem_" ++ tag ++ "_ok\n" ++
  -- Non-zero size expands/copies the range, so offset must be u64.
  "  ld x18, 8(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x18, 16(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x18, 24(x12)\n" ++
  "  bnez x18, .exit_outofgas\n" ++
  "  ld x14, 0(x12)\n" ++
  "  add x18, x14, x15\n" ++
  "  bltu x18, x14, .exit_outofgas\n" ++
  (if sparseWindows then
    "  la x19, evm_call_depth\n" ++
    "  ld x19, 0(x19)\n" ++
    "  bnez x19, .Lrrmem_nested_" ++ tag ++ "\n" ++
    "  li x19, " ++ toString rootRuntimeMemoryArenaLimitBytes ++ "\n" ++
    "  bltu x19, x18, .exit_outofgas\n" ++
    "  j .Lrrmem_guard_done_" ++ tag ++ "\n" ++
    ".Lrrmem_nested_" ++ tag ++ ":\n" ++
    "  la x16, create_frame_flag\n" ++
    "  slli x17, x19, 3\n" ++
    "  add x16, x16, x17\n" ++
    "  ld x16, 0(x16)\n" ++
    "  beqz x16, .Lrrmem_guard_done_" ++ tag ++ "\n" ++
    "  li x19, " ++ toString runtimeMemoryArenaLimitBytes ++ "\n" ++
    "  bltu x19, x18, .exit_outofgas\n" ++
    ".Lrrmem_guard_done_" ++ tag ++ ":\n"
   else
    memoryArenaLimitAsm ("return_" ++ tag) "x19" ++
    "  bltu x19, x18, .exit_outofgas\n") ++
  updateActiveMemorySizeAsm tag "x14" "x15" "x16" "x17" "x18" "x6" true ++
  ".Lreturn_revert_mem_" ++ tag ++ "_ok:\n"

/-- CALL-family memory expansion gas for the input and output windows.

    The dispatch loop and precompile bodies charge the static CALL base and
    precompile-specific inner gas separately; this helper charges only generic
    EVM memory expansion for `(in_offset, in_size)` and
    `(out_offset, out_size)`. Zero-size ranges do not expand memory, so high
    offset limbs are tolerated when the corresponding low size limb is zero.
    Non-zero high size limbs, high offsets for non-zero sizes, low-limb
    offset+size wraparound, and ranges past the current materialized memory arena
    route to `.exit_outofgas`.

    `sparseWindows = true` (call-frame guest only, evm-asm-0w05f.13 surface 3):
    the OUT window of a depth-1+ frame is charge-only — validity is decided by
    the quadratic expansion charge, and the write-back into the beyond-dense
    part is served by `sparse_window_write` at the child's RETURN/REVERT tail
    (frame descend path). The depth-0 root guard is kept verbatim. The IN
    window keeps the dense bail at every depth: child calldata is ALIASED into
    the parent's live memory (`call_frame_set_calldata`), so a beyond-dense
    args window has no materialized backing for the child's lifetime —
    conservative, and no known fixture needs it. The precompile dispatch
    branch re-imposes the dense OUT bound (`basicPrecompileCallTail`), since
    precompile outputs are written raw to `x13 + outoff`. -/
def callMemoryExpansionGasAsm
    (tag : String)
    (inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat)
    (sparseWindows : Bool := false) : String :=
  "  ld x15, " ++ toString inSizeOff ++ "(x12)\n" ++
  "  beqz x15, .Lcallmem_" ++ tag ++ "_out\n" ++
  "  ld x5, " ++ toString (inSizeOff + 8) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (inSizeOff + 16) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (inSizeOff + 24) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (inOffsetOff + 8) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (inOffsetOff + 16) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (inOffsetOff + 24) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x14, " ++ toString inOffsetOff ++ "(x12)\n" ++
  "  add x5, x14, x15\n" ++
  "  bltu x5, x14, .exit_outofgas\n" ++
  memoryArenaLimitAsm ("call_" ++ tag ++ "_in") "x6" ++
  "  bltu x6, x5, .exit_outofgas\n" ++
  updateActiveMemorySizeAsm ("call_" ++ tag ++ "_in") "x14" "x15" "x16" "x17" "x5" "x6" true ++
  ".Lcallmem_" ++ tag ++ "_out:\n" ++
  "  ld x15, " ++ toString outSizeOff ++ "(x12)\n" ++
  "  beqz x15, .Lcallmem_" ++ tag ++ "_done\n" ++
  "  ld x5, " ++ toString (outSizeOff + 8) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (outSizeOff + 16) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (outSizeOff + 24) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (outOffsetOff + 8) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (outOffsetOff + 16) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, " ++ toString (outOffsetOff + 24) ++ "(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x14, " ++ toString outOffsetOff ++ "(x12)\n" ++
  "  add x5, x14, x15\n" ++
  "  bltu x5, x14, .exit_outofgas\n" ++
  (if sparseWindows then
    "  la x6, evm_call_depth\n" ++
    "  ld x6, 0(x6)\n" ++
    "  bnez x6, .Lcallmem_" ++ tag ++ "_out_nested\n" ++
    "  li x6, " ++ toString rootRuntimeMemoryArenaLimitBytes ++ "\n" ++
    "  bltu x6, x5, .exit_outofgas\n" ++
    ".Lcallmem_" ++ tag ++ "_out_nested:\n"
   else
    memoryArenaLimitAsm ("call_" ++ tag ++ "_out") "x6" ++
    "  bltu x6, x5, .exit_outofgas\n") ++
  updateActiveMemorySizeAsm ("call_" ++ tag ++ "_out") "x14" "x15" "x16" "x17" "x5" "x6" true ++
  ".Lcallmem_" ++ tag ++ "_done:\n"

/-- CREATE-family initcode dynamic gas. The dispatch loop already charges
    `CREATE_ACCESS = 11000`; this charges the EIP-3860 initcode word
    cost `2 * ceil32(size) / 32`, and for CREATE2 also the EIP-1014 hashcost
    `6 * ceil32(size) / 32`. Memory expansion is handled separately by
    `updateActiveMemorySizeAsm` over the same initcode range.

    The caller must have already checked high size limbs and, for nonzero
    size, that high offset limbs and `offset + size` fit the runtime memory
    arena. `sizeReg` is preserved; `roundedReg`, `wordsReg`, and `gasReg` are
    clobbered. -/
def createInitcodeGasAsm
    (tag sizeReg roundedReg wordsReg gasReg : String) (hasSalt : Bool) :
    String :=
  let perWordCost := if hasSalt then 8 else 2
  "  beqz " ++ sizeReg ++ ", .Lcreate_initgas_" ++ tag ++ "_done\n" ++
  "  addi " ++ roundedReg ++ ", " ++ sizeReg ++ ", 31\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ sizeReg ++ ", .exit_outofgas\n" ++
  "  srli " ++ wordsReg ++ ", " ++ roundedReg ++ ", 5\n" ++
  "  li " ++ gasReg ++ ", " ++ toString perWordCost ++ "\n" ++
  "  mul " ++ gasReg ++ ", " ++ wordsReg ++ ", " ++ gasReg ++ "\n" ++
  "  ld " ++ roundedReg ++ ", 568(x20)\n" ++
  "  bltu " ++ roundedReg ++ ", " ++ gasReg ++ ", .exit_outofgas\n" ++
  "  sub " ++ roundedReg ++ ", " ++ roundedReg ++ ", " ++ gasReg ++ "\n" ++
  "  sd " ++ roundedReg ++ ", 568(x20)\n" ++
  ".Lcreate_initgas_" ++ tag ++ "_done:\n"

/-- EXP dynamic gas add-on before exponentiation. The dispatch loop already
    charges the fixed EXP base cost (10), so this charges only
    `50 * exponentByteLength(exponent)`.

    Stack layout before EXP body: `base` at 0(x12), `exponent` at 32(x12).
    EVM words are stored little-endian as four u64 limbs; the byte length is
    therefore the highest non-zero limb index times 8 plus that limb's own
    non-zero byte length. Scratch registers x5/x6/x7 are clobbered. -/
def expDynamicGasAsm : String :=
  "  li x6, 0\n" ++
  "  ld x5, 56(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb3\n" ++
  "  ld x5, 48(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb2\n" ++
  "  ld x5, 40(x12)\n" ++
  "  bnez x5, .Lexp_gas_limb1\n" ++
  "  ld x5, 32(x12)\n" ++
  "  beqz x5, .Lexp_gas_charge\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb1:\n" ++
  "  li x6, 8\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb2:\n" ++
  "  li x6, 16\n" ++
  "  j .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_limb3:\n" ++
  "  li x6, 24\n" ++
  ".Lexp_gas_count_limb:\n" ++
  "  addi x6, x6, 1\n" ++
  "  srli x5, x5, 8\n" ++
  "  bnez x5, .Lexp_gas_count_limb\n" ++
  ".Lexp_gas_charge:\n" ++
  "  li x7, 50\n" ++
  "  mul x6, x6, x7\n" ++
  "  ld x5, 568(x20)\n" ++
  "  bltu x5, x6, .exit_outofgas\n" ++
  "  sub x5, x5, x6\n" ++
  "  sd x5, 568(x20)\n"

/-- LOG0..LOG4 dynamic gas before event-log mutation. The dispatch loop already
    charges the fixed LOG base cost (375), so this charges only topic gas,
    data-byte gas, and memory expansion for the logged byte range. Per
    execution-specs, zero-size LOG does not expand memory, so high offset limbs
    are accepted when the low size limb is zero. Non-representable non-zero
    sizes and low-limb `offset + size` wraparound route to OOG.

    Stack layout before LOG body: `offset` at 0(x12), `size` at 32(x12), then
    `topicCount` topic words. Scratch registers x5/x6/x14/x15/x16/x17/x18 are
    clobbered. -/
def logDynamicGasAsm (topicCount : Nat) : String :=
  -- Any non-zero high size limb means size is non-zero but not representable.
  "  ld x5, 40(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 48(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 56(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x15, 32(x12)\n" ++
  -- x18 = topicCount * 375 + size * 8.
  "  li x18, " ++ toString (topicCount * 375) ++ "\n" ++
  "  li x5, 1\n" ++
  "  slli x5, x5, 61\n" ++
  "  bgeu x15, x5, .exit_outofgas\n" ++
  "  slli x5, x15, 3\n" ++
  "  add x18, x18, x5\n" ++
  "  beqz x15, .Llog" ++ toString topicCount ++ "_charge_dynamic\n" ++
  -- Non-zero size expands/captures the data range, so offset must be u64.
  "  ld x5, 8(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 16(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 24(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x14, 0(x12)\n" ++
  "  add x5, x14, x15\n" ++
  "  bltu x5, x14, .exit_outofgas\n" ++
  updateActiveMemorySizeAsm
    ("log" ++ toString topicCount) "x14" "x15" "x16" "x17" "x5" "x6" true ++
  ".Llog" ++ toString topicCount ++ "_charge_dynamic:\n" ++
  "  ld x5, 568(x20)\n" ++
  "  bltu x5, x18, .exit_outofgas\n" ++
  "  sub x5, x5, x18\n" ++
  "  sd x5, 568(x20)\n"

/-- Range guard for KECCAK256/SHA3 before dynamic gas or hashing. The runtime
    memory arena is u64-addressed; a non-zero high limb in `size` represents an
    astronomically large non-zero hash range, so it is reported as OOG. Per
    execution-specs, zero-size KECCAK does not expand memory, so high offset
    limbs are accepted when the low size limb is zero. Low-limb
    `offset + size` wraparound also routes to OOG. -/
def keccakRangeGuardAsm : String :=
  -- Any non-zero high size limb means size is non-zero but not representable.
  "  ld x5, 40(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 48(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 56(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x15, 32(x12)\n" ++
  "  beqz x15, .Lkeccak_range_ok\n" ++
  -- Non-zero size expands/hashes the input range, so offset must be u64.
  "  ld x5, 8(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 16(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x5, 24(x12)\n" ++
  "  bnez x5, .exit_outofgas\n" ++
  "  ld x14, 0(x12)\n" ++
  "  add x5, x14, x15\n" ++
  "  bltu x5, x14, .exit_outofgas\n" ++
  ".Lkeccak_range_ok:\n"

/-- KECCAK256/SHA3 word gas. The dispatch loop already charges the fixed
    opcode base cost (30), so this charges only `6 * ceil(size / 32)` against
    `env.gasRemaining`. `sizeReg` is preserved; x5/x6 are clobbered. -/
def keccakWordGasAsm (sizeReg : String) : String :=
  "  addi x5, " ++ sizeReg ++ ", 31\n" ++
  "  srli x5, x5, 5\n" ++
  "  slli x6, x5, 2\n" ++
  "  add x6, x6, x5\n" ++
  "  add x6, x6, x5\n" ++
  "  ld x5, 568(x20)\n" ++
  "  bltu x5, x6, .exit_outofgas\n" ++
  "  sub x5, x5, x6\n" ++
  "  sd x5, 568(x20)\n"

end EvmAsm.Codegen
