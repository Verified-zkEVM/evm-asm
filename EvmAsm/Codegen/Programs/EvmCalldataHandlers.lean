/-
  EvmAsm.Codegen.Programs.EvmCalldataHandlers

  Dispatcher handlers for calldata opcodes.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Calldata.LoadFullProgram
import EvmAsm.Evm64.Calldata.CopyProgram
import EvmAsm.Evm64.Calldata.SizeProgram
import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-- M13 calldata-context opcodes. Sibling to `envHandlers`: reads the
    `callDataLenOff = 424` cell from the same env block that M12
    initialises via `la x20, evm_env`.

    `evm_calldatasize` has the same 6-instruction shape as
    `evm_env_load`: load 8 bytes from `envBaseReg + 424`, decrement
    `x12` by 32, write the low limb and three zero high limbs. The
    M12 env-region size of 416 bytes is too small for offset 424;
    `Dispatch.lean`'s `evm_env:` block is bumped to 512 bytes in this
    PR (covers all `Environment/Layout.lean` fields up to
    `returnDataSizeOff = 440` + 8 with slack).

    The calldata-length cell is zero-initialised by the data section
    (same as the env fields), so `CALLDATASIZE` currently returns 0.
    Non-zero values come from a future host-preload PR.

    **M21 update**: the runtime-bytecode dispatcher's prologue now
    populates `env.callDataPtr` / `env.callDataLen` from the ziskemu
    `-i` input file. CALLDATALOAD (0x35) and CALLDATACOPY (0x37) wired
    here read real calldata bytes. The pre-M21 no-ops for both opcodes
    are removed from `popPushZeroHandlers` / `copyNoopHandlers` in
    `Programs/Noop.lean`. -/
def calldataHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_CALLDATASIZE"
    , opcodes := [0x36]
    , preBody := stackOverflowGuardAsm
    , body    := EvmAsm.Evm64.Calldata.evm_calldatasize .x20 .x15
    , tail    := .advanceAndRet 1 }
  , -- Verified CALLDATALOAD (0x35). The body is the full bounds-checked
    -- `evm_calldataload` (111 instructions): a 12-instruction dispatch
    -- OR-reduces offset limbs 1..3 and the `offset_lo >= len` bit and
    -- branches to a 4xSD zero arm; the in-bounds arm is the 94-instruction
    -- 32-byte window read (mirrors `evm_mload`), followed by a JAL to the
    -- common exit. Registry witness:
    -- `Calldata.evm_calldataload_stack_spec_within` (cpsTripleWithin 107)
    -- — unconditional in the operand (in-bounds, straddle, low-limb OOB,
    -- offsets >= 2^64 all covered).
    --
    -- lv44p.1 zero-pad, resolved: the witness's precondition
    -- (`CalldataRegionWf` + `paddedCallData`, Evm64/Calldata/Region.lean)
    -- requires `env.callDataPtr` to be 8-aligned and backed by
    -- `callDataLen + 32` addressable bytes with a 32-zero-byte tail. The
    -- padded-arena setup (PR #9871) establishes exactly this at every call
    -- frame (`bv_calldata_arena` bump allocations in
    -- `call_frame_set_calldata` + the top-level prologue copy), so the
    -- straddle window `offset < len < offset+32` reads real bytes then
    -- zeros — no staging buffer needed. The former `bv_cdl_stage`
    -- per-op staging loop is deleted.
    --
    -- Register instantiation (pinned by the `#guard`s in
    -- Evm64/Calldata/LoadFullProgram.lean): envBaseReg = x20 (read-only),
    -- clobbers {x14..x18, x5, x28, x29} — strictly narrower than the old
    -- staging preBody's {x5, x6, x7, x14, x28..x31}.
    { label   := "h_CALLDATALOAD"
    , opcodes := [0x35]
    , preBody := stackUnderflowGuardAsm 1
    , body    := EvmAsm.Evm64.Calldata.evm_calldataload
                   .x20 .x15 .x16 .x17 .x18 .x14 .x5 .x28 .x29
    , tail    := .advanceAndRet 1 }
  , -- M21 real CALLDATACOPY (0x37). The verified body
    -- `evm_calldatacopy` (19 instructions) pops `(destOffset, offset,
    -- size)`, loads `cdp` and `len` from env directly, and runs a
    -- byte loop that copies up to `size` bytes from
    -- `calldata[offset..]` into `memory[destOffset..]`, zero-filling
    -- bytes whose source address falls outside the calldata window.
    -- envBaseReg = x20 (set in dispatcher prologue); memBaseReg = x13
    -- (M7); the remaining 6 args are caller-saved scratch.
    { label   := "h_CALLDATACOPY"
    , opcodes := [0x37]
    , preBody := stackUnderflowGuardAsm 3 ++ "\n" ++
                 "  ld x14, 0(x12)\n" ++
                 "  ld x15, 64(x12)\n" ++
                 -- cdcoob.1: the copy body consumes only the low 64-bit source offset.
                 -- If any high limb is nonzero, or the low limb is already outside calldata,
                 -- normalize the source offset to callDataLen so the existing loop takes its
                 -- out-of-bounds zero-fill path without forming a wrapping `cdp + offset` pointer.
                 "  ld x16, 32(x12)\n" ++
                 "  ld x17, 40(x12)\n  ld x18, 48(x12)\n  or x17, x17, x18\n" ++
                 "  ld x18, 56(x12)\n  or x17, x17, x18\n" ++
                 "  bnez x17, 1f\n" ++
                 "  ld x18, 424(x20)\n  bltu x16, x18, 2f\n" ++
                 "1:\n" ++
                 "  ld x18, 424(x20)\n  sd x18, 32(x12)\n" ++
                 "2:\n" ++
                 memDynamicArenaOogGuardAsm "calldatacopy" "x14" "x15" "x16" "x17" ++
                 copyWordGasAsm "calldatacopy" "x15" "x16" "x17" "x18" ++
                 updateActiveMemorySizeAsm "calldatacopy" "x14" "x15" "x16" "x17" "x18" "x6" true
    , body    := EvmAsm.Evm64.Calldata.evm_calldatacopy
                   .x20 .x13 .x14 .x15 .x16 .x17 .x18 .x19
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
