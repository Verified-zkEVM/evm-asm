/-
  EvmAsm.Codegen.Programs.EvmMcopyHandlers

  Dispatcher handler for MCOPY.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmMcopyGas
import EvmAsm.Codegen.Programs.EvmMemoryGas

namespace EvmAsm.Codegen

/-- EIP-5656 MCOPY for the concrete dispatcher. The handler rejects
    unsupported 256-bit memory ranges, consumes low u64 limbs for
    `(dest, src, length)`, charges dynamic gas, updates MSIZE for both
    read and write ranges, then performs `memmove`-style byte copying
    so overlapping ranges are handled correctly. -/
def mcopyHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MCOPY"
      opcodes := [0x5e]
      preBody := stackUnderflowGuardAsm 3
      body    := []
      tail    := .custom <|
        "  ld x14, 0(x12)\n" ++          -- destination offset
        "  ld x15, 32(x12)\n" ++         -- source offset
        "  ld x16, 64(x12)\n" ++         -- length
        mcopyRangeGuardAsm ++
        mcopyDynamicGasAsm ++
        "  addi x12, x12, 96\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        updateActiveMemorySizeAsm "mcopy_src" "x15" "x16" "x17" "x18" "x19" "x6" false ++
        updateActiveMemorySizeAsm "mcopy_dst" "x14" "x16" "x17" "x18" "x19" "x6" false ++
        "  add x17, x13, x14\n" ++       -- destination pointer
        "  add x18, x13, x15\n" ++       -- source pointer
        "  add x19, x15, x16\n" ++       -- source end offset
        "  bleu x14, x15, .Lmcopy_forward\n" ++
        "  bgeu x14, x19, .Lmcopy_forward\n" ++
        "  add x17, x17, x16\n" ++
        "  add x18, x18, x16\n" ++
        ".Lmcopy_backward_loop:\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        "  addi x17, x17, -1\n" ++
        "  addi x18, x18, -1\n" ++
        "  lbu x19, 0(x18)\n" ++
        "  sb x19, 0(x17)\n" ++
        "  addi x16, x16, -1\n" ++
        "  j .Lmcopy_backward_loop\n" ++
        ".Lmcopy_forward:\n" ++
        "  beqz x16, .Lmcopy_done\n" ++
        "  lbu x19, 0(x18)\n" ++
        "  sb x19, 0(x17)\n" ++
        "  addi x18, x18, 1\n" ++
        "  addi x17, x17, 1\n" ++
        "  addi x16, x16, -1\n" ++
        "  j .Lmcopy_forward\n" ++
        ".Lmcopy_done:\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
