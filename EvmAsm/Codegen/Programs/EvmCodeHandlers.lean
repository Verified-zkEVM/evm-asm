/-
  EvmAsm.Codegen.Programs.EvmCodeHandlers

  Dispatcher handlers for CODESIZE and CODECOPY.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Evm64.Code.CopyProgram
import EvmAsm.Evm64.Code.SizeProgram

namespace EvmAsm.Codegen

/-- M33: running-code opcodes CODESIZE (0x38) and CODECOPY (0x39).
    Both operate on the *currently executing* bytecode, which the
    dispatcher already holds in memory: code base in `x21` and exact
    byte length in the `env+codeSizeOff` (= 496) cell, seeded by both
    dispatcher prologues. No witness / external-account state is needed
    (unlike BALANCE / EXTCODE*), so these are self-contained.

    - **CODESIZE** mirrors the MSIZE/GAS env-cell-push shape: push
      `env.codeSize` as a 256-bit word (low limb = length, high limbs 0).
    - **CODECOPY** pops `(destOffset, dataOffset, size)` and runs the
      verified `Code.evm_codecopy` byte loop (sibling of CALLDATACOPY),
      copying `code[dataOffset..]` into `memory[destOffset..]` with
      zero-fill past `len(code)`. The `preBody` charges memory expansion
      (`updateActiveMemorySizeAsm`) over the destination range and guards
      against stack underflow (3 operands). -/
def codeHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_CODESIZE"
      opcodes := [0x38]
      preBody := stackOverflowGuardAsm
      body    := EvmAsm.Evm64.Code.evm_codesize .x20 .x14
      tail    := .advanceAndRet 1 }
  , { label   := "h_CODECOPY"
      opcodes := [0x39]
      preBody := stackUnderflowGuardAsm 3 ++ "\n" ++
                 "  ld x14, 0(x12)\n" ++        -- destOffset low limb (MSIZE range)
                 "  ld x15, 64(x12)\n" ++       -- size low limb (MSIZE range)
                 memDynamicU256RangeOogGuardAsm
                   "codecopy" "x12" "x15" "x16" "x17" 0 64 ++
                 -- CODECOPY zero-fills every byte whose full-U256 source index
                 -- is outside the running code.  The body consumes only the
                 -- low limb, so normalize an unrepresentable/out-of-range
                 -- source to codeSize before it can form a wrapped pointer.
                 "  ld x16, 32(x12)\n" ++
                 "  ld x17, 40(x12)\n  ld x18, 48(x12)\n  or x17, x17, x18\n" ++
                 "  ld x18, 56(x12)\n  or x17, x17, x18\n" ++
                 "  bnez x17, .Lcodecopy_oob_source\n" ++
                 "  ld x18, 496(x20)\n  bltu x16, x18, .Lcodecopy_source_ok\n" ++
                 ".Lcodecopy_oob_source:\n" ++
                 "  ld x18, 496(x20)\n  sd x18, 32(x12)\n" ++
                 ".Lcodecopy_source_ok:\n" ++
                 memDynamicArenaOogGuardAsm "codecopy" "x14" "x15" "x16" "x17" ++
                 copyWordGasAsm "codecopy" "x15" "x16" "x17" "x18" ++
                 updateActiveMemorySizeAsm "codecopy" "x14" "x15" "x16" "x17" "x18" "x6" true false
      body    := EvmAsm.Evm64.Code.evm_codecopy
                   .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18
      tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
