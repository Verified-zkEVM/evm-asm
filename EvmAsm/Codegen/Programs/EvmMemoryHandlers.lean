/-
  EvmAsm.Codegen.Programs.EvmMemoryHandlers

  Dispatcher handlers for MLOAD, MSTORE, MSTORE8, and MSIZE.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.MLoad.Program
import EvmAsm.Evm64.MStore.Program
import EvmAsm.Evm64.MStore8.Program
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-! ## memory opcode handler families -/

/-- M7 memory opcodes. Register-parameterized; the dispatcher
    prologue sets up `x13 = &evm_memory` (see
    `EvmAsm/Codegen/Dispatch.lean`). The scratch registers `x14..x18`
    are caller-saved across the `jalr` from the dispatcher loop;
    nothing else in the registry preserves them.

    Stack-pointer bookkeeping is internal to the verified bodies:
    `evm_mload` is net stack-neutral, while `evm_mstore` and
    `evm_mstore8` each end with `ADDI .x12 .x12 64` so the wrapper
    uses the standard `.advanceAndRet 1` tail. None of the memory
    opcodes touch `x10`, so no `preBody` is needed. -/
def memoryHandlers : List OpcodeHandlerSpec :=
  [ -- MLOAD: pop offset, push value. memBase=x13;
    -- scratch: offReg=x15, byteReg=x16, accReg=x17, addrReg=x18.
    { label   := "h_MLOAD"
      opcodes := [0x51]
      preBody := stackUnderflowGuardAsm 1 ++ "\n" ++
                 "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mload" "x15" "x16" "x17" "x18" "x19" "x6" true 32
      body    := EvmAsm.Evm64.evm_mload .x15 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE: pop offset + value, write 32 bytes BE to memory.
    -- valReg=x14 (scratch; placeholder per evm_mstore docstring).
    { label   := "h_MSTORE"
      opcodes := [0x52]
      preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mstore" "x15" "x16" "x17" "x18" "x19" "x6" true 32
      body    := EvmAsm.Evm64.evm_mstore .x15 .x14 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE8: pop offset + value, write 1 byte to memory.
    { label   := "h_MSTORE8"
      opcodes := [0x53]
      preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstAsm "mstore8" "x15" "x16" "x17" "x18" "x19" "x6" true 1
      body    := EvmAsm.Evm64.evm_mstore8 .x15 .x14 .x18 .x13
      tail    := .advanceAndRet 1 } ]

/-- MSIZE pushes the dispatcher-maintained active memory size. It is
    updated by the concrete memory handlers in this file using the
    EVM's 32-byte rounding rule. -/
def memoryMetadataHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MSIZE"
      opcodes := [0x59]
      body    := []
      tail    := .custom <|
        "  addi x12, x12, -32\n" ++
        "  ld x14, " ++ toString activeMemorySizeOff ++ "(x20)\n" ++
        "  sd x14, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
