/-
  EvmAsm.Codegen.Programs.EvmDivModHandlers

  Dispatcher handlers for unsigned DIV and MOD.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Codegen.Programs.EvmDivModWrappers

namespace EvmAsm.Codegen

private def divModTail : HandlerTail :=
  .custom "  mv x10, x14\n  addi x10, x10, 1\n  ret"

def divModHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_DIV"
      opcodes := [0x04]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmDivPatched
      tail    := divModTail }
  , { label   := "h_MOD"
      opcodes := [0x06]
      preBody := stackUnderflowGuardAsm 2 ++ "\n  mv x14, x10"
      body    := evmModPatched
      tail    := divModTail } ]

end EvmAsm.Codegen
