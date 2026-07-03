/-
  EvmAsm.Evm64.AddMod

  Umbrella for the ADDMOD opcode subtree (GH #91). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.AddMod`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `addmod_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.AddMod.AddrNormAttr
import EvmAsm.Evm64.AddMod.Program
import EvmAsm.Evm64.AddMod.ProgramTest
import EvmAsm.Evm64.AddMod.Args
import EvmAsm.Evm64.AddMod.ArgsStackDecode
import EvmAsm.Evm64.AddMod.StackExecutionBridge
import EvmAsm.Evm64.AddMod.LimbSpec
import EvmAsm.Evm64.AddMod.Pow256Spec
import EvmAsm.Evm64.AddMod.Pow256CodeBridge
import EvmAsm.Evm64.AddMod.AddrNorm
import EvmAsm.Evm64.AddMod.Compose.Base
import EvmAsm.Evm64.AddMod.Compose.TotalBase
import EvmAsm.Evm64.AddMod.Compose.CarryBlockSpecs
import EvmAsm.Evm64.AddMod.Compose.CondSubSpec
import EvmAsm.Evm64.AddMod.Compose.CallAdapter
import EvmAsm.Evm64.AddMod.Compose.CarryBranch
import EvmAsm.Evm64.AddMod.Compose.ZeroBranch
import EvmAsm.Evm64.AddMod.Spec

import EvmAsm.Evm64.AddMod.LiveStackPost
