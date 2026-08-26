/-
  EvmAsm.Evm64.SMod

  Umbrella for the SMOD opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SMod`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `smod_addr` attribute exists when later modules
  attach lemmas to it.
-/

module

public import EvmAsm.Evm64.SMod.AddrNormAttr
public import EvmAsm.Evm64.SMod.Args
public import EvmAsm.Evm64.SMod.ArgsStackDecode
public import EvmAsm.Evm64.SMod.StackExecutionBridge
public import EvmAsm.Evm64.SMod.HandlerBridge
public import EvmAsm.Evm64.SMod.Program
public import EvmAsm.Evm64.SMod.LimbSpec
public import EvmAsm.Evm64.SMod.AddrNorm
public import EvmAsm.Evm64.SMod.Compose.BaseOffsets
public import EvmAsm.Evm64.SMod.Compose.CodeHandles
public import EvmAsm.Evm64.SMod.Compose.BaseCode
public import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost
public import EvmAsm.Evm64.SMod.Compose.ModCallCallable
public import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
public import EvmAsm.Evm64.SMod.Compose.Words
public import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
public import EvmAsm.Evm64.SMod.Compose.Bridges
public import EvmAsm.Evm64.SMod.Compose.AbsComponents
public import EvmAsm.Evm64.SMod.Compose.DispatchReadyView
public import EvmAsm.Evm64.SMod.Compose.ModCallPost
public import EvmAsm.Evm64.SMod.Compose.ModCallBzeroHandoff
public import EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixView
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn
public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost
public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix
public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixGeneric
public import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixNamedPost
public import EvmAsm.Evm64.SMod.Compose.SavedRaRet
public import EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame
public import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric
public import EvmAsm.Evm64.SMod.Compose.ModCallReturnNamedPost
public import EvmAsm.Evm64.SMod.Compose.ModCallReturnNormalized
public import EvmAsm.Evm64.SMod.Compose.SaveRa
public import EvmAsm.Evm64.SMod.Compose.SignBlockSpecs
public import EvmAsm.Evm64.SMod.Compose.PreserveDividendSign
public import EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs
public import EvmAsm.Evm64.SMod.Compose.ModCall
public import EvmAsm.Evm64.SMod.Compose.SaveRaSignSequence
public import EvmAsm.Evm64.SMod.Compose.PreserveDividendSignSequence
public import EvmAsm.Evm64.SMod.Compose.DivisorSignSequence
public import EvmAsm.Evm64.SMod.Compose.DividendAbsSequence
public import EvmAsm.Evm64.SMod.Compose.DivisorAbsSequence
public import EvmAsm.Evm64.SMod.Compose.ModCallSequence
public import EvmAsm.Evm64.SMod.Compose.ModCallDispatchReadySequence
public import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
public import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
public import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5
public import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5
public import EvmAsm.Evm64.SMod.ModCallV5Shared
public import EvmAsm.Evm64.SMod.Spec
public import EvmAsm.Evm64.SMod.SpecSemantic
public import EvmAsm.Evm64.SMod.SpecBzero
public import EvmAsm.Evm64.SMod.SpecAllCase
meta import EvmAsm.Evm64.SMod.AddrNormAttr
meta import EvmAsm.Evm64.SMod.Args
meta import EvmAsm.Evm64.SMod.ArgsStackDecode
meta import EvmAsm.Evm64.SMod.StackExecutionBridge
meta import EvmAsm.Evm64.SMod.HandlerBridge
meta import EvmAsm.Evm64.SMod.Program
meta import EvmAsm.Evm64.SMod.LimbSpec
meta import EvmAsm.Evm64.SMod.AddrNorm
meta import EvmAsm.Evm64.SMod.Compose.BaseOffsets
meta import EvmAsm.Evm64.SMod.Compose.CodeHandles
meta import EvmAsm.Evm64.SMod.Compose.BaseCode
meta import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost
meta import EvmAsm.Evm64.SMod.Compose.ModCallCallable
meta import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
meta import EvmAsm.Evm64.SMod.Compose.Words
meta import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
meta import EvmAsm.Evm64.SMod.Compose.Bridges
meta import EvmAsm.Evm64.SMod.Compose.AbsComponents
meta import EvmAsm.Evm64.SMod.Compose.DispatchReadyView
meta import EvmAsm.Evm64.SMod.Compose.ModCallPost
meta import EvmAsm.Evm64.SMod.Compose.ModCallBzeroHandoff
meta import EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff
meta import EvmAsm.Evm64.SMod.Compose.ResultSignFixView
meta import EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree
meta import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn
meta import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost
meta import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix
meta import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixGeneric
meta import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixNamedPost
meta import EvmAsm.Evm64.SMod.Compose.SavedRaRet
meta import EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame
meta import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric
meta import EvmAsm.Evm64.SMod.Compose.ModCallReturnNamedPost
meta import EvmAsm.Evm64.SMod.Compose.ModCallReturnNormalized
meta import EvmAsm.Evm64.SMod.Compose.SaveRa
meta import EvmAsm.Evm64.SMod.Compose.SignBlockSpecs
meta import EvmAsm.Evm64.SMod.Compose.PreserveDividendSign
meta import EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs
meta import EvmAsm.Evm64.SMod.Compose.ModCall
meta import EvmAsm.Evm64.SMod.Compose.SaveRaSignSequence
meta import EvmAsm.Evm64.SMod.Compose.PreserveDividendSignSequence
meta import EvmAsm.Evm64.SMod.Compose.DivisorSignSequence
meta import EvmAsm.Evm64.SMod.Compose.DividendAbsSequence
meta import EvmAsm.Evm64.SMod.Compose.DivisorAbsSequence
meta import EvmAsm.Evm64.SMod.Compose.ModCallSequence
meta import EvmAsm.Evm64.SMod.Compose.ModCallDispatchReadySequence
meta import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
meta import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
meta import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5
meta import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5
meta import EvmAsm.Evm64.SMod.ModCallV5Shared
meta import EvmAsm.Evm64.SMod.Spec
meta import EvmAsm.Evm64.SMod.SpecSemantic
meta import EvmAsm.Evm64.SMod.SpecBzero
meta import EvmAsm.Evm64.SMod.SpecAllCase
public meta import Lean.Meta.Tactic.Simp.Attr

@[expose] public section
