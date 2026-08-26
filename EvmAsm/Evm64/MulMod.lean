/-
  EvmAsm.Evm64.MulMod

  Umbrella for the MULMOD opcode subtree (GH #91). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.MulMod`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `mulmod_addr` attribute exists when later modules
  attach lemmas to it.
-/

module

public import EvmAsm.Evm64.MulMod.AddrNormAttr
public import EvmAsm.Evm64.MulMod.Layout
public import EvmAsm.Evm64.MulMod.Program
public import EvmAsm.Evm64.MulMod.ProductAlgebra
public import EvmAsm.Evm64.MulMod.ReduceSemantics
public import EvmAsm.Evm64.MulMod.ReduceCorrect
public import EvmAsm.Evm64.MulMod.ReduceFoldInvariant
public import EvmAsm.Evm64.MulMod.ReducePerLimb
public import EvmAsm.Evm64.MulMod.ReduceOuterHorner
public import EvmAsm.Evm64.MulMod.ProductLimbsValue
public import EvmAsm.Evm64.MulMod.ReduceCarryAgree
public import EvmAsm.Evm64.MulMod.ReduceShift
public import EvmAsm.Evm64.MulMod.ReduceCompare
public import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
public import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
public import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
public import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract
public import EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs
public import EvmAsm.Evm64.MulMod.ReduceBitLoop
public import EvmAsm.Evm64.MulMod.ReduceOuterLoop
public import EvmAsm.Evm64.MulMod.ReduceOuterInduction
public import EvmAsm.Evm64.MulMod.LimbSpec
public import EvmAsm.Evm64.MulMod.AddPartialSpecs
public import EvmAsm.Evm64.MulMod.AddPartialTable
public import EvmAsm.Evm64.MulMod.ProductLayoutLifts
public import EvmAsm.Evm64.MulMod.ProductLayoutCall05
public import EvmAsm.Evm64.MulMod.ProductLayoutCall06
public import EvmAsm.Evm64.MulMod.ProductLayoutCall07
public import EvmAsm.Evm64.MulMod.ProductLayoutCall08
public import EvmAsm.Evm64.MulMod.ProductLayoutCall09
public import EvmAsm.Evm64.MulMod.ProductLayoutCall10
public import EvmAsm.Evm64.MulMod.ProductLayoutCall11
public import EvmAsm.Evm64.MulMod.ProductLayoutCall12
public import EvmAsm.Evm64.MulMod.ProductLayoutCall13
public import EvmAsm.Evm64.MulMod.ProductLayoutCall14
public import EvmAsm.Evm64.MulMod.ProductLayoutCall15
public import EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra
public import EvmAsm.Evm64.MulMod.ProductLayoutCall05Carry
public import EvmAsm.Evm64.MulMod.ProductLayoutCall09Carry
public import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Call02Feed
public import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Target
public import EvmAsm.Evm64.MulMod.ProductLayoutColumn5Target
public import EvmAsm.Evm64.MulMod.ProductLayoutColumn6Target
public import EvmAsm.Evm64.MulMod.ProductLayoutColumn7Target
public import EvmAsm.Evm64.MulMod.ProductLayoutHighTargets
public import EvmAsm.Evm64.MulMod.ProductLayoutSpec
public import EvmAsm.Evm64.MulMod.AddrNorm
public import EvmAsm.Evm64.MulMod.MulModResultWord
public import EvmAsm.Evm64.MulMod.Compose.Base
public import EvmAsm.Evm64.MulMod.Compose.Reducer
public import EvmAsm.Evm64.MulMod.Compose.ProductCore
public import EvmAsm.Evm64.MulMod.Compose.ProductSuffix
public import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge
public import EvmAsm.Evm64.MulMod.Compose.ProductReduce
public import EvmAsm.Evm64.MulMod.Compose.ProductReduceValue
public import EvmAsm.Evm64.MulMod.Compose.ZeroPathBody
public import EvmAsm.Evm64.MulMod.Compose.ZeroPathTail
public import EvmAsm.Evm64.MulMod.Compose.Dispatch
public import EvmAsm.Evm64.MulMod.Compose.DispatchZero
public import EvmAsm.Evm64.MulMod.Compose.DispatchAll
public import EvmAsm.Evm64.MulMod.Compose.StackSpec
public import EvmAsm.Evm64.MulMod.Compose.StackSpecAll
public import EvmAsm.Evm64.MulMod.Spec
meta import EvmAsm.Evm64.MulMod.AddrNormAttr
meta import EvmAsm.Evm64.MulMod.Layout
meta import EvmAsm.Evm64.MulMod.Program
meta import EvmAsm.Evm64.MulMod.ProductAlgebra
meta import EvmAsm.Evm64.MulMod.ReduceSemantics
meta import EvmAsm.Evm64.MulMod.ReduceCorrect
meta import EvmAsm.Evm64.MulMod.ReduceFoldInvariant
meta import EvmAsm.Evm64.MulMod.ReducePerLimb
meta import EvmAsm.Evm64.MulMod.ReduceOuterHorner
meta import EvmAsm.Evm64.MulMod.ProductLimbsValue
meta import EvmAsm.Evm64.MulMod.ReduceCarryAgree
meta import EvmAsm.Evm64.MulMod.ReduceShift
meta import EvmAsm.Evm64.MulMod.ReduceCompare
meta import EvmAsm.Evm64.MulMod.ReduceInnerStepPrefix
meta import EvmAsm.Evm64.MulMod.ReduceInnerStepCompare
meta import EvmAsm.Evm64.MulMod.ReduceInnerStepTail
meta import EvmAsm.Evm64.MulMod.ReduceInnerStepSubtract
meta import EvmAsm.Evm64.MulMod.ReduceInnerStepSpecs
meta import EvmAsm.Evm64.MulMod.ReduceBitLoop
meta import EvmAsm.Evm64.MulMod.ReduceOuterLoop
meta import EvmAsm.Evm64.MulMod.ReduceOuterInduction
meta import EvmAsm.Evm64.MulMod.LimbSpec
meta import EvmAsm.Evm64.MulMod.AddPartialSpecs
meta import EvmAsm.Evm64.MulMod.AddPartialTable
meta import EvmAsm.Evm64.MulMod.ProductLayoutLifts
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall05
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall06
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall07
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall08
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall09
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall10
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall11
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall12
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall13
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall14
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall15
meta import EvmAsm.Evm64.MulMod.ProductLayoutPublicAlgebra
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall05Carry
meta import EvmAsm.Evm64.MulMod.ProductLayoutCall09Carry
meta import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Call02Feed
meta import EvmAsm.Evm64.MulMod.ProductLayoutColumn4Target
meta import EvmAsm.Evm64.MulMod.ProductLayoutColumn5Target
meta import EvmAsm.Evm64.MulMod.ProductLayoutColumn6Target
meta import EvmAsm.Evm64.MulMod.ProductLayoutColumn7Target
meta import EvmAsm.Evm64.MulMod.ProductLayoutHighTargets
meta import EvmAsm.Evm64.MulMod.ProductLayoutSpec
meta import EvmAsm.Evm64.MulMod.AddrNorm
meta import EvmAsm.Evm64.MulMod.MulModResultWord
meta import EvmAsm.Evm64.MulMod.Compose.Base
meta import EvmAsm.Evm64.MulMod.Compose.Reducer
meta import EvmAsm.Evm64.MulMod.Compose.ProductCore
meta import EvmAsm.Evm64.MulMod.Compose.ProductSuffix
meta import EvmAsm.Evm64.MulMod.Compose.ProductReduceBridge
meta import EvmAsm.Evm64.MulMod.Compose.ProductReduce
meta import EvmAsm.Evm64.MulMod.Compose.ProductReduceValue
meta import EvmAsm.Evm64.MulMod.Compose.ZeroPathBody
meta import EvmAsm.Evm64.MulMod.Compose.ZeroPathTail
meta import EvmAsm.Evm64.MulMod.Compose.Dispatch
meta import EvmAsm.Evm64.MulMod.Compose.DispatchZero
meta import EvmAsm.Evm64.MulMod.Compose.DispatchAll
meta import EvmAsm.Evm64.MulMod.Compose.StackSpec
meta import EvmAsm.Evm64.MulMod.Compose.StackSpecAll
meta import EvmAsm.Evm64.MulMod.Spec
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section

