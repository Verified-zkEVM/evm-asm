/-
  EvmAsm.Evm64.Add.Program

  256-bit EVM ADD program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM ADD: binary, pops 2, pushes 1.
    Limb 0: LD, LD, ADD, SLTU (carry), SD (5 instructions).
    Limbs 1-3: LD, LD, ADD, SLTU (carry1), ADD (carryIn), SLTU (carry2), OR (carryOut), SD (8 each).
    Then ADDI sp, sp, 32.
    Registers: x12=sp, x7=acc, x6=operand, x5=carry, x11=carry1. -/
def evm_add : Program :=
  -- Limb 0 (5 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;;
  ADD .x7 .x7 .x6 ;; SLTU .x5 .x7 .x6 ;; SD .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  ADD .x7 .x7 .x6 ;; SLTU .x11 .x7 .x6 ;;
  ADD .x7 .x7 .x5 ;; SLTU .x6 .x7 .x5 ;;
  OR' .x5 .x11 .x6 ;; SD .x12 .x7 40 ;;
  -- Limb 2 (8 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  ADD .x7 .x7 .x6 ;; SLTU .x11 .x7 .x6 ;;
  ADD .x7 .x7 .x5 ;; SLTU .x6 .x7 .x5 ;;
  OR' .x5 .x11 .x6 ;; SD .x12 .x7 48 ;;
  -- Limb 3 (8 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  ADD .x7 .x7 .x6 ;; SLTU .x11 .x7 .x6 ;;
  ADD .x7 .x7 .x5 ;; SLTU .x6 .x7 .x5 ;;
  OR' .x5 .x11 .x6 ;; SD .x12 .x7 56 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

end EvmAsm.Evm64
