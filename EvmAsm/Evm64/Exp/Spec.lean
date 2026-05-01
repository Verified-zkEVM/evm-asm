/-
  EvmAsm.Evm64.Exp.Spec

  Top-level (semantic / stack-level) cpsTriple spec for `evm_exp`,
  bridging the limb-level loop composition to a single `evmWordIs`
  pre/post pair.

  Skeleton placeholder for GH #92 (beads slice evm-asm-cf2c). The actual
  `evm_exp_stack_spec` / `evm_exp_stack_spec_within` theorem lands in the
  semantic slice (evm-asm-6snn).
-/

import EvmAsm.Evm64.Exp.Compose.Base

namespace EvmAsm.Evm64

open EvmAsm.Rv64

-- Placeholder: `evm_exp_stack_spec_within` lands in slice 6 (evm-asm-6snn).

end EvmAsm.Evm64
