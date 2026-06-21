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

/-- Guard the HIGH 192 bits of a 256-bit memory offset (stack word at `0(x12)`,
    low limb at +0, high limbs at +8/+16/+24) for the fixed-length memory opcodes
    MLOAD/MSTORE/MSTORE8. The access length is a nonzero constant (1 or 32), so the
    EVM always touches memory and `offset + length` must fit the memory cost model;
    any offset >= 2^64 (a nonzero high limb) makes the word count and quadratic
    memory-expansion cost astronomically large — execution-specs
    `calculate_gas_extend_memory` then OOGs on `charge_gas`. So route a nonzero high
    limb straight to `.exit_outofgas` (matching the existing high-limb guards in
    `returnRevertMemoryGasAsm` / `callMemoryExpansionGasAsm` / `keccakRangeGuardAsm`,
    which `updateActiveMemorySizeAsm` itself does NOT perform — it only sees the low
    limb). `tmpReg` is clobbered; must be free before `updateActiveMemorySize*`. -/
def fixedMemoryOffsetHighLimbGuardAsm (tmpReg : String) : String :=
  "  ld " ++ tmpReg ++ ", 8(x12)\n" ++
  "  bnez " ++ tmpReg ++ ", .exit_outofgas\n" ++
  "  ld " ++ tmpReg ++ ", 16(x12)\n" ++
  "  bnez " ++ tmpReg ++ ", .exit_outofgas\n" ++
  "  ld " ++ tmpReg ++ ", 24(x12)\n" ++
  "  bnez " ++ tmpReg ++ ", .exit_outofgas\n"

/-- `updateActiveMemorySizeAsm` for a constant access length (MLOAD/MSTORE =
    32, MSTORE8 = 1). Materializes the length into `tmpLengthReg` first. -/
def updateActiveMemorySizeConstAsm
    (tag offsetReg tmpLengthReg roundedReg currentReg maskReg gasTmpReg : String)
    (chargeGas : Bool) (length : Nat) : String :=
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
    wraparound, or an end past the current 32 KiB runtime memory arena route
    to `.exit_outofgas` before any return/revert output is emitted.

    Stack layout before RETURN/REVERT body: `offset` at `0(x12)`, `size` at
    `32(x12)`. Scratch registers x14/x15/x16/x17/x18/x19/x6 are clobbered. -/
def returnRevertMemoryGasAsm (tag : String) : String :=
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
  "  li x19, 0x8000\n" ++
  "  bltu x19, x18, .exit_outofgas\n" ++
  updateActiveMemorySizeAsm tag "x14" "x15" "x16" "x17" "x18" "x6" true ++
  ".Lreturn_revert_mem_" ++ tag ++ "_ok:\n"

/-- CALL-family memory expansion gas for the input and output windows.

    The dispatch loop and precompile bodies charge the static CALL base and
    precompile-specific inner gas separately; this helper charges only generic
    EVM memory expansion for `(in_offset, in_size)` and
    `(out_offset, out_size)`. Zero-size ranges do not expand memory, so high
    offset limbs are tolerated when the corresponding low size limb is zero.
    Non-zero high size limbs, high offsets for non-zero sizes, and low-limb
    offset+size wraparound route to `.exit_outofgas`. -/
def callMemoryExpansionGasAsm
    (tag : String)
    (inOffsetOff inSizeOff outOffsetOff outSizeOff : Nat) : String :=
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
  updateActiveMemorySizeAsm ("call_" ++ tag ++ "_out") "x14" "x15" "x16" "x17" "x5" "x6" true ++
  ".Lcallmem_" ++ tag ++ "_done:\n"

/-- CREATE-family initcode dynamic gas. The dispatch loop already charges
    `OPCODE_CREATE_BASE = 9000`; this charges the EIP-3860 initcode word
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
