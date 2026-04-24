/-
  EvmAsm.Evm64.Pop.Program

  256-bit EVM POP: discard top of stack, sp += 32.
  1 instruction (ADDI x12 x12 32).
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

def evm_pop : Program := ADDI .x12 .x12 32

abbrev evm_pop_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_pop

end EvmAsm.Evm64
