/-
  EvmAsm.Evm64.MulMod

  Umbrella for the MULMOD opcode subtree (GH #91). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.MulMod`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `mulmod_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.MulMod.AddrNormAttr
import EvmAsm.Evm64.MulMod.Layout
import EvmAsm.Evm64.MulMod.Program
import EvmAsm.Evm64.MulMod.ProductAlgebra
import EvmAsm.Evm64.MulMod.LimbSpec
import EvmAsm.Evm64.MulMod.AddPartialSpecs
import EvmAsm.Evm64.MulMod.AddPartialTable
import EvmAsm.Evm64.MulMod.ProductLayoutLifts
import EvmAsm.Evm64.MulMod.ProductLayoutCall05
import EvmAsm.Evm64.MulMod.ProductLayoutCall06
import EvmAsm.Evm64.MulMod.ProductLayoutCall07
import EvmAsm.Evm64.MulMod.ProductLayoutCall08
import EvmAsm.Evm64.MulMod.ProductLayoutCall09
import EvmAsm.Evm64.MulMod.ProductLayoutCall10
import EvmAsm.Evm64.MulMod.ProductLayoutCall11
import EvmAsm.Evm64.MulMod.ProductLayoutCall12
import EvmAsm.Evm64.MulMod.ProductLayoutCall13
import EvmAsm.Evm64.MulMod.AddrNorm
import EvmAsm.Evm64.MulMod.Compose.Base
import EvmAsm.Evm64.MulMod.Compose.ProductCore
import EvmAsm.Evm64.MulMod.Compose.ProductSuffix
import EvmAsm.Evm64.MulMod.Spec
