/-
  EvmAsm.Evm64.SMod

  Umbrella for the SMOD opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SMod`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `smod_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.SMod.AddrNormAttr
import EvmAsm.Evm64.SMod.Layout
import EvmAsm.Evm64.SMod.Args
import EvmAsm.Evm64.SMod.ArgsStackDecode
import EvmAsm.Evm64.SMod.StackExecutionBridge
import EvmAsm.Evm64.SMod.HandlerBridge
import EvmAsm.Evm64.SMod.Program
import EvmAsm.Evm64.SMod.LimbSpec
import EvmAsm.Evm64.SMod.AddrNorm
import EvmAsm.Evm64.SMod.Compose.Base
import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5
import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5
import EvmAsm.Evm64.SMod.Compose.ModCallExactCallableV5
import EvmAsm.Evm64.SMod.Compose.ModCallExactHandoffV5
import EvmAsm.Evm64.SMod.Compose.PrefixChainV5
import EvmAsm.Evm64.SMod.Spec
import EvmAsm.Evm64.SMod.SpecSemantic
import EvmAsm.Evm64.SMod.SpecBzero
import EvmAsm.Evm64.SMod.SpecAllCase
