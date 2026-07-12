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



def sparseMemoryStoreWordAsm (tag : String) : String :=
  -- x15 holds the low offset limb and memory gas/MSIZE has already been charged.
  memoryArenaLimitAsm ("sparse_store_" ++ tag) "x18" ++
  "  addi x17, x15, 32
" ++
  "  bltu x17, x15, .exit_outofgas
" ++
  "  bgeu x18, x17, .Lsparse_store_" ++ tag ++ "_dense
" ++
  "  la x18, evm_sparse_memory_count
" ++
  "  ld x17, 0(x18)
" ++
  "  li x19, " ++ toString sparseMemoryWordCapacity ++ "
" ++
  "  bgeu x17, x19, .exit_outofgas
" ++
  "  la x19, evm_sparse_memory_entries
" ++
  "  slli x6, x17, 5
" ++
  "  slli x16, x17, 4
" ++
  "  add x6, x6, x16
" ++
  "  add x19, x19, x6
" ++
  "  la x6, evm_call_depth
" ++
  "  ld x6, 0(x6)
" ++
  "  sd x6, 0(x19)
" ++
  "  sd x15, 8(x19)
" ++
  "  ld x6, 32(x12); sd x6, 16(x19)
" ++
  "  ld x6, 40(x12); sd x6, 24(x19)
" ++
  "  ld x6, 48(x12); sd x6, 32(x19)
" ++
  "  ld x6, 56(x12); sd x6, 40(x19)
" ++
  "  addi x17, x17, 1
" ++
  "  sd x17, 0(x18)
" ++
  "  addi x12, x12, 64
" ++
  "  addi x10, x10, 1
" ++
  "  ret
" ++
  ".Lsparse_store_" ++ tag ++ "_dense:
"

def sparseMemoryLoadWordAsm (tag : String) : String :=
  -- x15 holds the low offset limb and memory gas/MSIZE has already been charged.
  memoryArenaLimitAsm ("sparse_load_" ++ tag) "x18" ++
  "  addi x17, x15, 32
" ++
  "  bltu x17, x15, .exit_outofgas
" ++
  "  bgeu x18, x17, .Lsparse_load_" ++ tag ++ "_dense
" ++
  "  sd x0, 0(x12); sd x0, 8(x12); sd x0, 16(x12); sd x0, 24(x12)
" ++
  "  la x18, evm_sparse_memory_count
" ++
  "  ld x17, 0(x18)
" ++
  "  la x19, evm_call_depth
" ++
  "  ld x19, 0(x19)
" ++
  "  beqz x17, .Lsparse_load_" ++ tag ++ "_done
" ++
  "  la x18, evm_sparse_memory_entries
" ++
  ".Lsparse_load_" ++ tag ++ "_loop:
" ++
  "  addi x17, x17, -1
" ++
  "  slli x6, x17, 5
" ++
  "  slli x16, x17, 4
" ++
  "  add x6, x6, x16
" ++
  "  add x6, x18, x6
" ++
  "  ld x16, 0(x6)
" ++
  "  bne x16, x19, .Lsparse_load_" ++ tag ++ "_next
" ++
  "  ld x16, 8(x6)
" ++
  "  bne x16, x15, .Lsparse_load_" ++ tag ++ "_next
" ++
  "  ld x16, 16(x6); sd x16, 0(x12)
" ++
  "  ld x16, 24(x6); sd x16, 8(x12)
" ++
  "  ld x16, 32(x6); sd x16, 16(x12)
" ++
  "  ld x16, 40(x6); sd x16, 24(x12)
" ++
  "  j .Lsparse_load_" ++ tag ++ "_done
" ++
  ".Lsparse_load_" ++ tag ++ "_next:
" ++
  "  bnez x17, .Lsparse_load_" ++ tag ++ "_loop
" ++
  ".Lsparse_load_" ++ tag ++ "_done:
" ++
  "  addi x10, x10, 1
" ++
  "  ret
" ++
  ".Lsparse_load_" ++ tag ++ "_dense:
"

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
                 updateActiveMemorySizeConstSparseAsm "mload" "x15" "x16" "x17" "x18" "x19" "x6" true 32 ++
                 sparseMemoryLoadWordAsm "mload"
      body    := EvmAsm.Evm64.evm_mload .x15 .x16 .x17 .x18 .x13
      tail    := .advanceAndRet 1 }
  , -- MSTORE: pop offset + value, write 32 bytes BE to memory.
    -- valReg=x14 (scratch; placeholder per evm_mstore docstring).
    { label   := "h_MSTORE"
      opcodes := [0x52]
      preBody := stackUnderflowGuardAsm 2 ++ "\n" ++
                 "  ld x15, 0(x12)\n" ++
                 updateActiveMemorySizeConstSparseAsm "mstore" "x15" "x16" "x17" "x18" "x19" "x6" true 32 ++
                 sparseMemoryStoreWordAsm "mstore"
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
      preBody := stackOverflowGuardAsm
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
