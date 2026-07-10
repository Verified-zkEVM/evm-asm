/-
  EvmAsm.Codegen.Programs.EvmCalldataHandlers

  Dispatcher handlers for calldata opcodes.
-/

import EvmAsm.Evm64.Calldata.LoadProgram
import EvmAsm.Evm64.Calldata.StageProgram
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
  , -- M21 real CALLDATALOAD (0x35), arena-free & VERIFIED (bead evm-asm-t1iqb).
    -- The whole body is the verified `evm_calldataload_staged` program
    -- (`Calldata/StageProgram.lean`, 121 instructions = 27-instruction
    -- zero-padded staging loop ;; the 94-instruction `evm_calldataload_window`
    -- ladder), proven end-to-end in `Calldata/StageSpec.lean`
    -- (`evm_calldataload_staged_stack_spec_within`, classical-3): it pops the
    -- 256-bit offset, materializes the zero-padded 32-byte CALLDATALOAD window
    -- into the aligned 64-byte `bv_cdl_stage` buffer (out-of-bounds positions
    -- yield the EVM-mandated zero pad — `stage[i] = cdp[normOff+i]` in bounds,
    -- 0 otherwise), then re-runs the window ladder over that buffer at offset 0
    -- and writes the packed word back to the EVM stack slot.
    --
    -- The `preBody` only does the stack-underflow guard and materializes the
    -- buffer base into x14 (a linker `la`, not a fixed-offset instruction);
    -- everything else is the verified Program. x20 = env, x12 = sp (dispatcher
    -- prologue); the body's first instruction is `ld x5, 416(x20)`.
    { label   := "h_CALLDATALOAD"
    , opcodes := [0x35]
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++
                 "  la x14, bv_cdl_stage\n"      -- x14 = stage base (survives into body)
    , body    := EvmAsm.Evm64.Calldata.evm_calldataload_staged
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
                 memDynamicU256RangeOogGuardAsm
                   "calldatacopy" "x12" "x15" "x17" "x18" 0 64 ++
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
