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
import EvmAsm.Evm64.MulMod.ReduceSemantics
import EvmAsm.Evm64.MulMod.ReduceCorrect
import EvmAsm.Evm64.MulMod.ReduceFoldInvariant
import EvmAsm.Evm64.MulMod.ReducePerLimb
import EvmAsm.Evm64.MulMod.ReduceOuterHorner
import EvmAsm.Evm64.MulMod.ProductLimbsValue
import EvmAsm.Evm64.MulMod.ReduceCarryAgree
import EvmAsm.Evm64.MulMod.ReduceShift
import EvmAsm.Evm64.MulMod.ReduceCompare
import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract
import EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs
import EvmAsm.Evm64.MulMod.ReduceBitLoop
import EvmAsm.Evm64.MulMod.ReduceOuterLoop
import EvmAsm.Evm64.MulMod.ReduceOuterInduction
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
import EvmAsm.Evm64.MulMod.ProductLayoutCall14
import EvmAsm.Evm64.MulMod.ProductLayoutCall15
import EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra
import EvmAsm.Evm64.MulMod.ProductLayoutCall05Carry
import EvmAsm.Evm64.MulMod.ProductLayoutCall09Carry
import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Call02Feed
import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Target
import EvmAsm.Evm64.MulMod.ProductLayoutColumn5Target
import EvmAsm.Evm64.MulMod.ProductLayoutColumn6Target
import EvmAsm.Evm64.MulMod.ProductLayoutColumn7Target
import EvmAsm.Evm64.MulMod.ProductLayoutHighTargets
import EvmAsm.Evm64.MulMod.ProductLayoutSpec
import EvmAsm.Evm64.MulMod.AddrNorm
import EvmAsm.Evm64.MulMod.MulModResultWord
import EvmAsm.Evm64.MulMod.Compose.Base
import EvmAsm.Evm64.MulMod.Compose.Reducer
import EvmAsm.Evm64.MulMod.Compose.ProductCore
import EvmAsm.Evm64.MulMod.Compose.ProductSuffix
import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge
import EvmAsm.Evm64.MulMod.Compose.ProductReduce
import EvmAsm.Evm64.MulMod.Compose.ProductReduceValue
import EvmAsm.Evm64.MulMod.Compose.ZeroPathBody
import EvmAsm.Evm64.MulMod.Compose.ZeroPathTail
import EvmAsm.Evm64.MulMod.Compose.Dispatch
import EvmAsm.Evm64.MulMod.Compose.DispatchZero
import EvmAsm.Evm64.MulMod.Compose.DispatchAll
import EvmAsm.Evm64.MulMod.Compose.StackSpec
import EvmAsm.Evm64.MulMod.Compose.StackSpecAll
import EvmAsm.Evm64.MulMod.Spec

