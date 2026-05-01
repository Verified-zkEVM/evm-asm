/-
  EvmAsm.Evm64.Exp.Program

  256-bit EVM EXP opcode (`EXP(a, b) = a^b mod 2^256`) as a 64-bit RISC-V
  program.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c).

  The actual Program will be defined in the Program-definition slice
  (evm-asm-ahaz). Per `docs/92-exp-survey.md` the algorithm is binary
  square-and-multiply over 256 bits of exponent, invoking `evm_mul`
  (made callable via a `cc_ret` shim) once per squaring and conditionally
  once per set bit. The full bytecode will be assembled from sub-blocks
  `exp_prologue`, `exp_square_block`, `exp_cond_mul_block`, `exp_iter_body`,
  `exp_loop`, `exp_epilogue`.

  This file currently has no `evm_exp` definition; later slices will add
  it without breaking the umbrella import graph.
-/

import EvmAsm.Evm64.Stack

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: `evm_exp : Program` lands in slice 3 (evm-asm-ahaz).
-- See `docs/92-exp-survey.md` for the algorithm and reuse points.

end EvmAsm.Evm64
