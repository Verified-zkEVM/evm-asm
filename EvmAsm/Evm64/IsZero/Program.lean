/-
  EvmAsm.Evm64.IsZero.Program

  256-bit EVM ISZERO program definition.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

/-- 256-bit EVM ISZERO: unary (pop 1, push 1, sp unchanged).
    OR all 4 limbs into x7, then SLTIU x7, x7, 1 (x7 = x7 == 0 ? 1 : 0).
    Store 256-bit result: limb[0] = x7, limbs[1-3] = 0 (via x0).
    12 instructions total. -/
def evm_iszero : Program :=
  -- OR reduction: load limb 0, then load & OR limbs 1-3 (7 instructions)
  LD .x7 .x12 0 ;;
  LD .x6 .x12 8  ;; single (.OR .x7 .x7 .x6) ;;
  LD .x6 .x12 16 ;; single (.OR .x7 .x7 .x6) ;;
  LD .x6 .x12 24 ;; single (.OR .x7 .x7 .x6) ;;
  -- Convert to boolean (1 instruction)
  single (.SLTIU .x7 .x7 1) ;;
  -- Store 256-bit result: limb[0] = x7, limbs[1-3] = 0 (4 instructions)
  SD .x12 .x7 0 ;;
  SD .x12 .x0 8 ;; SD .x12 .x0 16 ;; SD .x12 .x0 24

end EvmAsm.Evm64
