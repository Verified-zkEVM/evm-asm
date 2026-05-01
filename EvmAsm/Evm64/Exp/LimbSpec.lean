/-
  EvmAsm.Evm64.Exp.LimbSpec

  Per-block / per-limb cpsTriple specs for EXP sub-blocks (square block,
  conditional-multiply block, iter body, loop, prologue, epilogue).

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c). Concrete specs
  will land in the LimbSpec-definition slice (evm-asm-mtj3). Per
  `OPCODE_TEMPLATE.md`, each sub-block gets exactly one cpsTriple lemma.
-/

import EvmAsm.Evm64.Exp.Program
import EvmAsm.Rv64.SyscallSpecs
import EvmAsm.Rv64.Tactics.XSimp
import EvmAsm.Rv64.Tactics.RunBlock

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: per-sub-block specs land in slice 4 (evm-asm-mtj3).

end EvmAsm.Evm64
