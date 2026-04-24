/-
  EvmAsm.Evm64.Eq.Program

  256-bit EVM EQ program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM EQ: binary (pop 2, push 1, sp += 32).
    XOR each limb pair, OR-reduce all XORs, SLTIU to boolean.
    21 instructions total. -/
def evm_eq : Program :=
  -- Limb 0 (3 instructions): XOR
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.XOR .x7 .x7 .x6) ;;
  -- Limb 1 (4 instructions): XOR + OR-accumulate
  LD .x6 .x12 8 ;; LD .x5 .x12 40 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 2 (4 instructions)
  LD .x6 .x12 16 ;; LD .x5 .x12 48 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Limb 3 (4 instructions)
  LD .x6 .x12 24 ;; LD .x5 .x12 56 ;; single (.XOR .x6 .x6 .x5) ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert to boolean + sp adjustment + store (6 instructions)
  single (.SLTIU .x7 .x7 1) ;;
  ADDI .x12 .x12 32 ;;
  SD .x12 .x7 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

end EvmAsm.Evm64
