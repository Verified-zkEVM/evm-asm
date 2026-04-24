/-
  EvmAsm.Evm64.Gt.Program

  256-bit EVM GT program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM GT: binary (pop 2, push 1, sp += 32).
    GT(a, b) = LT(b, a): swap load order vs evm_lt.
    26 instructions total. -/
def evm_gt : Program :=
  -- Limb 0 (3 instructions): load b into x7, a into x6
  LD .x7 .x12 32 ;; LD .x6 .x12 0 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions)
  LD .x7 .x12 40 ;; LD .x6 .x12 8 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 48 ;; LD .x6 .x12 16 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 3 (6 instructions)
  LD .x7 .x12 56 ;; LD .x6 .x12 24 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- sp adjustment + store 256-bit result (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

end EvmAsm.Evm64
