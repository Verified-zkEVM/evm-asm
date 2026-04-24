/-
  EvmAsm.Evm64.Not.Program

  256-bit EVM NOT program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM NOT: unary (pop 1, push 1, sp unchanged).
    For each limb: load, XOR with -1 (complement), store back. -/
def evm_not : Program :=
  LD .x7 .x12 0 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 0 ;;
  LD .x7 .x12 8 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 8 ;;
  LD .x7 .x12 16 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 16 ;;
  LD .x7 .x12 24 ;; XORI .x7 .x7 (-1) ;; SD .x12 .x7 24

end EvmAsm.Evm64
