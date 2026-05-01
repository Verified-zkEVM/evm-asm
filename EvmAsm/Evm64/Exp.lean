/-
  EvmAsm.Evm64.Exp

  Umbrella for the EXP opcode subtree (GH #92). Re-exports the top-level
  spec; downstream consumers should `import EvmAsm.Evm64.Exp` and not
  reach into sub-modules directly.

  AddrNormAttr is imported first (per AGENTS.md `register_simp_attr`
  ordering rule) so the `exp_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.Exp.AddrNormAttr
import EvmAsm.Evm64.Exp.Program
import EvmAsm.Evm64.Exp.LimbSpec
import EvmAsm.Evm64.Exp.AddrNorm
import EvmAsm.Evm64.Exp.Compose.Base
import EvmAsm.Evm64.Exp.Spec
