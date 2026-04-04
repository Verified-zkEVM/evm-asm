/-
  EvmAsm.Evm64.Push0.Program

  256-bit EVM PUSH0: push 0 onto stack, sp -= 32.
  5 instructions (ADDI + 4 × SD x0).
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

def evm_push0 : Program :=
  ADDI .x12 .x12 (-32) ;;
  SD .x12 .x0 0 ;; SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

abbrev evm_push0_code (base : Word) : CodeReq :=
  CodeReq.ofProg base evm_push0

end EvmAsm.Rv64
