/-
  EvmAsm.Codegen.Programs.EvmCodeHandlers

  Dispatcher handlers for CODESIZE and CODECOPY.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas
import EvmAsm.Evm64.Code.CopyProgram

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
      body    := []
      tail    := .custom <|
        "  addi x12, x12, -32\n" ++
        "  ld x14, " ++ toString EvmAsm.Evm64.Code.codeSizeOff ++ "(x20)\n" ++
        "  sd x14, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" }
  , { label   := "h_CODECOPY"
      opcodes := [0x39]
      preBody := stackUnderflowGuardAsm 3 ++ "\n" ++
                 "  ld x14, 0(x12)\n" ++        -- destOffset low limb (MSIZE range)
                 "  ld x15, 64(x12)\n" ++       -- size low limb (MSIZE range)
                 copyWordGasAsm "codecopy" "x15" "x16" "x17" "x18" ++
                 updateActiveMemorySizeAsm "codecopy" "x14" "x15" "x16" "x17" "x18" "x6" true
      body    := EvmAsm.Evm64.Code.evm_codecopy
                   .x20 .x13 .x21 .x14 .x15 .x16 .x17 .x18
      tail    := .advanceAndRet 1 } ]

end EvmAsm.Codegen
