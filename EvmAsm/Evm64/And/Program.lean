/-
  EvmAsm.Evm64.And.Program

  256-bit EVM AND program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM AND: binary, pops 2, pushes 1.
    For each of 4 limbs: load A[i] and B[i], AND them, store to B[i].
    Then advance sp by 32. -/
def evm_and : Program :=
  LD .x7 .x12 0 ;; LD .x6 .x12 32 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 32 ;;
  LD .x7 .x12 8 ;; LD .x6 .x12 40 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 40 ;;
  LD .x7 .x12 16 ;; LD .x6 .x12 48 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 48 ;;
  LD .x7 .x12 24 ;; LD .x6 .x12 56 ;; single (.AND .x7 .x7 .x6) ;; SD .x12 .x7 56 ;;
  ADDI .x12 .x12 32

end EvmAsm.Evm64
