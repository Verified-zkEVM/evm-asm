/-
  EvmAsm.Codegen.Programs.EvmMulmodHandler

  Dispatcher handler for MULMOD.
-/

import EvmAsm.Codegen.Dispatch
import EvmAsm.Evm64.MulMod.Program

namespace EvmAsm.Codegen

/-- MULMOD's verified body uses x10/x13/x20 internally, so the dispatcher
    wrapper saves and restores those live runtime registers around it.

    NB: x21 is the dispatcher's permanent code base (the dispatch loop reads
    `sub x5, x10, x21` every iteration; s4/s5 = x20/x21 are env/code base and
    must never be used as scratch). The earlier wrapper used x21 as the save
    slot for x13, clobbering the code base so the codeSize guard ran on
    garbage after MULMOD (bv_fail=37 on `vmArithmeticTest/mulmod`). Save x13
    into x28 (t3) instead: it is neither dispatcher-live nor touched by
    `evm_mulmod` (whose body is straight-line, no nested calls). -/
private def mulmodTail : HandlerTail :=
  .custom <|
    "  mv x10, x23\n" ++
    "  mv x13, x28\n" ++
    "  mv x20, x22\n" ++
    "  addi x10, x10, 1\n" ++
    "  ret"

def mulmodHandlers : List OpcodeHandlerSpec :=
  [ { label   := "h_MULMOD"
      opcodes := [0x09]
      preBody := stackUnderflowGuardAsm 3 ++ "\n  mv x23, x10\n  mv x28, x13\n  mv x22, x20"
      body    := EvmAsm.Evm64.evm_mulmod
      tail    := mulmodTail } ]

end EvmAsm.Codegen
