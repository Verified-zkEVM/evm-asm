/-
  EvmAsm.Codegen.Programs.EvmMulmodHandler

  Dispatcher handler for MULMOD.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.MulMod.Program

namespace EvmAsm.Codegen

/-- MULMOD's verified body uses x10/x13/x20 internally, so the dispatcher
    wrapper saves and restores those live runtime registers around it. -/
private def mulmodTail : HandlerTail :=
  .custom <|
    "  mv x10, x23\n" ++
    "  mv x13, x21\n" ++
    "  mv x20, x22\n" ++
    "  addi x10, x10, 1\n" ++
    "  ret"

def mulmodHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MULMOD"
      opcodes := [0x09]
      preBody := stackUnderflowGuardAsm 3 ++ "\n  mv x23, x10\n  mv x21, x13\n  mv x22, x20"
      body    := EvmAsm.Evm64.evm_mulmod
      tail    := mulmodTail } ]

end EvmAsm.Codegen
