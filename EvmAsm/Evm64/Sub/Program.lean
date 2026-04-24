/-
  EvmAsm.Evm64.Sub.Program

  256-bit EVM SUB program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM SUB: binary, pops 2, pushes 1.
    Limb 0: LD, LD, SLTU (borrow), SUB, SD (5 instructions).
    Limbs 1-3: LD, LD, SLTU (borrow1), SUB, SLTU (borrow2), SUB (borrowIn), OR (borrowOut), SD (8 each).
    Then ADDI sp, sp, 32. -/
def evm_sub : Program :=
  -- Limb 0 (5 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;;
  single (.SLTU .x5 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  -- Limb 1 (8 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 40 ;;
  -- Limb 2 (8 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 48 ;;
  -- Limb 3 (8 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.SUB .x7 .x7 .x5) ;;
  single (.OR .x5 .x11 .x6) ;; SD .x12 .x7 56 ;;
  -- sp adjustment
  ADDI .x12 .x12 32

end EvmAsm.Evm64
