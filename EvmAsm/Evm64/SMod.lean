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
import EvmAsm.Evm64.SMod.Compose.BaseOffsets
import EvmAsm.Evm64.SMod.Compose.CodeHandles
import EvmAsm.Evm64.SMod.Compose.BaseCode
import EvmAsm.Evm64.SMod.Compose.DispatchReadyPost
import EvmAsm.Evm64.SMod.Compose.ModCallCallable
import EvmAsm.Evm64.SMod.Compose.BaseTopLevel
import EvmAsm.Evm64.SMod.Compose.Words
import EvmAsm.Evm64.SMod.Compose.QuadMemBridges
import EvmAsm.Evm64.SMod.Compose.Bridges
import EvmAsm.Evm64.SMod.Compose.AbsComponents
import EvmAsm.Evm64.SMod.Compose.DispatchReadyView
import EvmAsm.Evm64.SMod.Compose.ModCallPost
import EvmAsm.Evm64.SMod.Compose.ModCallBzeroHandoff
import EvmAsm.Evm64.SMod.Compose.ModCallGenericHandoff
import EvmAsm.Evm64.SMod.Compose.ResultSignFixView
import EvmAsm.Evm64.SMod.Compose.ResultSignFixPCFree
import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixPost
import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFix
import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixGeneric
import EvmAsm.Evm64.SMod.Compose.ModCallResultSignFixNamedPost
import EvmAsm.Evm64.SMod.Compose.SavedRaRet
import EvmAsm.Evm64.SMod.Compose.SavedRaRetFrame
import EvmAsm.Evm64.SMod.Compose.ModCallReturnGeneric
import EvmAsm.Evm64.SMod.Compose.ModCallReturnNamedPost
import EvmAsm.Evm64.SMod.Compose.ModCallReturnNormalized
import EvmAsm.Evm64.SMod.Compose.SaveRa
import EvmAsm.Evm64.SMod.Compose.SignBlockSpecs
import EvmAsm.Evm64.SMod.Compose.PreserveDividendSign
import EvmAsm.Evm64.SMod.Compose.AbsBlockSpecs
import EvmAsm.Evm64.SMod.Compose.ModCall
import EvmAsm.Evm64.SMod.Compose.SaveRaSignSequence
import EvmAsm.Evm64.SMod.Compose.PreserveDividendSignSequence
import EvmAsm.Evm64.SMod.Compose.DivisorSignSequence
import EvmAsm.Evm64.SMod.Compose.DividendAbsSequence
import EvmAsm.Evm64.SMod.Compose.DivisorAbsSequence
import EvmAsm.Evm64.SMod.Compose.ModCallSequence
import EvmAsm.Evm64.SMod.Compose.ModCallDispatchReadySequence
import EvmAsm.Evm64.SMod.Compose.CodeHandlesV5
import EvmAsm.Evm64.SMod.Compose.BaseCodeV5
import EvmAsm.Evm64.SMod.Compose.BaseSpecsV5
import EvmAsm.Evm64.SMod.Compose.ResultSignFixOwnV5
import EvmAsm.Evm64.SMod.ModCallV5Shared
import EvmAsm.Evm64.SMod.Spec
import EvmAsm.Evm64.SMod.SpecSemantic
import EvmAsm.Evm64.SMod.SpecBzero
import EvmAsm.Evm64.SMod.SpecAllCase
