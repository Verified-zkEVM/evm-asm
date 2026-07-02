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
    , preBody := stackOverflowGuardAsm
    , body    := EvmAsm.Evm64.Calldata.evm_calldatasize .x20 .x15
    , tail    := .advanceAndRet 1 }
  , -- M21 real CALLDATALOAD (0x35). The verified body
    -- `evm_calldataload_window` (94 instructions, mirrors `evm_mload`)
    -- handles the in-bounds 32-byte read: pop offset, compute
    -- `base + offset`, pack 4 BE u64 limbs via LBU/SLLI/OR, write the
    -- result back to the same EVM stack slot.
    --
    -- lv44p.1 zero-pad: the verified body does a RAW 32-byte read with
    -- no out-of-bounds guard, so bytes past `env.callDataLen` would pick
    -- up adjacent memory — a soundness bug (garbage instead of the
    -- EVM-mandated zero padding; observed as a spurious storage write +
    -- state-gas overcharge on a contract that CALLDATALOADs past the end
    -- of a short calldata). The `preBody` stages a zero-padded 32-byte
    -- window into `bv_cdl_stage`, then points the body's base register
    -- (x14) at that buffer with a zeroed stack offset, so the body packs
    -- the padded window. In-bounds bytes are byte-identical to the direct
    -- read (`stage[i] = cdp[offset+i]`); only out-of-bounds positions
    -- change (garbage -> 0). The staging is NON-in-place — it writes only
    -- the fixed scratch buffer and the offset's low limb on the EVM stack,
    -- never a computed x12-relative byte address (which crashed an earlier
    -- in-place mask attempt in nested/aliased-calldata frames). Numeric
    -- local labels keep it correct under any multi-emit of the registry.
    { label   := "h_CALLDATALOAD"
    , opcodes := [0x35]
    , preBody := stackUnderflowGuardAsm 1 ++ "\n" ++
                 "  ld x5, 416(x20)\n" ++          -- x5 = cdp (env.callDataPtr)
                 "  ld x6, 424(x20)\n" ++          -- x6 = callDataLen
                 "  ld x7, 0(x12)\n" ++            -- x7 = offset low limb
                 "  ld x28, 8(x12)\n" ++           -- offset limbs 1..3 (high)
                 "  ld x29, 16(x12)\n" ++
                 "  ld x30, 24(x12)\n" ++
                 "  or x28, x28, x29\n" ++
                 "  or x28, x28, x30\n" ++         -- x28 != 0  <=>  offset >= 2^64
                 "  sltu x29, x7, x6\n" ++         -- x29 = (offset_lo < len)
                 "  seqz x29, x29\n" ++            -- x29 = (offset_lo >= len)
                 "  or x28, x28, x29\n" ++         -- x28 = skip-all flag (entire window OOB)
                 "  la x14, bv_cdl_stage\n" ++     -- x14 = stage base (survives into body)
                 "  li x29, 0\n" ++                -- i = 0
                 "1:\n" ++
                 "  li x30, 32\n" ++
                 "  beq x29, x30, 3f\n" ++
                 "  add x31, x14, x29\n" ++        -- &stage[i]
                 "  sb x0, 0(x31)\n" ++            -- stage[i] = 0 (default pad byte)
                 "  bnez x28, 2f\n" ++             -- entire window OOB -> leave 0
                 "  add x30, x7, x29\n" ++         -- pos = offset_lo + i (no u64 overflow: offset_lo < len here)
                 "  bgeu x30, x6, 2f\n" ++         -- pos >= len -> OOB -> leave 0
                 "  add x30, x5, x30\n" ++         -- &cdp[pos]
                 "  lbu x30, 0(x30)\n" ++
                 "  sb x30, 0(x31)\n" ++           -- stage[i] = cdp[pos]
                 "2:\n" ++
                 "  addi x29, x29, 1\n" ++
                 "  j 1b\n" ++
                 "3:\n" ++
                 "  sd x0, 0(x12)\n"              -- zero offset low limb: body reads stage_base+0
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
