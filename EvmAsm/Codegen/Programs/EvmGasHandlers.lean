/-
  EvmAsm.Codegen.Programs.EvmGasHandlers

  Dispatcher handler for the GAS opcode.
-/

import EvmAsm.Codegen.Dispatch

namespace EvmAsm.Codegen

/-- M30: GAS (0x5a) pushes the dispatcher-maintained remaining gas
    (env+568, charged per-opcode by the dispatch loop). Mirrors the
    MSIZE handler — read the env cell, push it as a 256-bit word (low
    limb = remaining gas, high limbs 0). The loop charges GAS's own
    cost (BASE = 2) *before* this handler runs, so the pushed value
    already reflects it, matching EVM semantics. -/
def gasHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_GAS"
      opcodes := [0x5a]
      body    := []
      tail    := .custom <|
        "  addi x12, x12, -32\n" ++
        "  ld x14, 568(x20)\n" ++       -- env.gasRemaining (M30)
        "  sd x14, 0(x12)\n" ++
        "  sd x0, 8(x12)\n" ++
        "  sd x0, 16(x12)\n" ++
        "  sd x0, 24(x12)\n" ++
        "  addi x10, x10, 1\n" ++
        "  ret" } ]

end EvmAsm.Codegen
