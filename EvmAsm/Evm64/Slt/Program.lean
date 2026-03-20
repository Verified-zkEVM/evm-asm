/-
  EvmAsm.Evm64.Slt.Program

  256-bit EVM SLT program definition.
-/

import EvmAsm.Evm64.Stack
import EvmAsm.Rv64.CPSSpec

namespace EvmAsm.Rv64

/-- 256-bit EVM SLT (Signed Less Than): binary (pop 2, push 1, sp += 32).
    Compare MSB limbs (limb 3) with signed RV64 SLT instruction.
    If MSB limbs equal, fall through to unsigned borrow chain on limbs 0-2.
    25 instructions total. -/
def evm_slt : Program :=
  -- Phase 1: Load MSB limbs and branch (3 instructions)
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;;
  single (.BEQ .x7 .x6 12) ;;
  -- MSB differ path (2 instructions): signed compare + jump to store
  single (.SLT .x5 .x7 .x6) ;; single (.JAL .x0 64) ;;
  -- Lower compare path: 3-limb unsigned borrow chain (15 instructions)
  -- Limb 0 (3 instructions)
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.SLTU .x5 .x7 .x6) ;;
  -- Limb 1 (6 instructions)
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Limb 2 (6 instructions)
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;;
  single (.SLTU .x11 .x7 .x6) ;; single (.SUB .x7 .x7 .x6) ;;
  single (.SLTU .x6 .x7 .x5) ;; single (.OR .x5 .x11 .x6) ;;
  -- Store phase (5 instructions)
  ADDI .x12 .x12 32 ;;
  SD .x12 .x5 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

end EvmAsm.Rv64
