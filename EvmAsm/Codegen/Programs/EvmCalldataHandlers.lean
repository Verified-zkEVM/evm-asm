/-
  EvmAsm.Codegen.Programs.EvmCalldataHandlers

  Dispatcher handlers for calldata opcodes.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
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
    , body    := EvmAsm.Evm64.Calldata.evm_calldatasize .x20 .x15
    , tail    := .advanceAndRet 1 }
  , -- M21 real CALLDATALOAD (0x35). The verified body
    -- `evm_calldataload_window` (94 instructions, mirrors `evm_mload`)
    -- handles the in-bounds 32-byte read: pop offset, compute
    -- `cdp + offset`, pack 4 BE u64 limbs via LBU/SLLI/OR, write the
    -- result back to the same EVM stack slot. The `preBody` loads
    -- the calldata pointer from `env.callDataPtrOff = 416` into x14
    -- (the body's `envPtrReg`).
    --
    -- Known limitation: in-bounds only. Reads past `cdp + callDataLen`
    -- yield whatever's in adjacent memory (typically zeros in the
    -- input region's padding, but undefined in general). A future PR
    -- can wrap with a bounds-check / zero-pad outer block. For
    -- trusted test programs that respect bounds, this is correct.
    { label   := "h_CALLDATALOAD"
    , opcodes := [0x35]
    , preBody := stackUnderflowGuardAsm 1 ++ "\n  ld x14, 416(x20)\n"
    , body    := EvmAsm.Evm64.Calldata.evm_calldataload_window
                   .x15 .x16 .x17 .x18 .x14
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
                 copyWordGasAsm "calldatacopy" "x15" "x16" "x17" "x18" ++
                 updateActiveMemorySizeAsm "calldatacopy" "x14" "x15" "x16" "x17" "x18" "x6" true
    , body    := EvmAsm.Evm64.Calldata.evm_calldatacopy
                   .x20 .x13 .x14 .x15 .x16 .x17 .x18 .x19
    , tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
