/-
  EvmAsm.Codegen.Programs.NoopReturnData

  RETURNDATASIZE/RETURNDATACOPY runtime handlers split out of `Programs.Noop`.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-- Runtime RETURNDATASIZE / RETURNDATACOPY handlers backed by
    `evm_precompile_frame`. -/
def returnDataHandlers : List OpcodeHandlerSpec :=
  [ { label := "h_RETURNDATASIZE", opcodes := [0x3d]
    , body := []
    , tail := .custom <|
        "  la x14, evm_precompile_frame\n" ++
        "  ld x15, 8(x14)\n" ++
        "  addi x12, x12, -32\n" ++
        "  sd x15, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" }
  , { label := "h_RETURNDATACOPY", opcodes := [0x3e]
    , body := []
    , tail := .custom <|
        "  ld x14, 0(x12)\n" ++
        "  ld x15, 32(x12)\n" ++
        "  ld x16, 64(x12)\n" ++
        "  la x17, evm_precompile_frame\n" ++
        "  ld x18, 8(x17)\n" ++
        "  add x19, x15, x16\n" ++
        "  bltu x19, x15, .exit_invalid\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        "  li x18, 256\n" ++
        "  bltu x18, x19, .exit_invalid\n" ++
        copyWordGasAsm "returndatacopy" "x16" "x17" "x18" "x19" ++
        updateActiveMemorySizeAsm "returndatacopy" "x14" "x16" "x17" "x18" "x19" "x6" true ++
        "  addi x12, x12, 96\n" ++
        "  beqz x16, 2f\n" ++
        "  la x17, evm_precompile_frame\n" ++
        "  addi x17, x17, 16\n" ++
        "  add x17, x17, x15\n" ++
        "  add x18, x13, x14\n" ++
        "1:\n" ++
        "  lbu x19, 0(x17)\n" ++
        "  sb x19, 0(x18)\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x18, x18, 1\n" ++
        "  addi x16, x16, -1\n" ++
        "  bnez x16, 1b\n" ++
        "2:\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
