/-
  EvmAsm.Evm64.SDiv

  Umbrella for the SDIV opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SDiv`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `sdiv_addr` attribute exists when later modules
  attach lemmas to it.
-/

import EvmAsm.Evm64.SDiv.AddrNormAttr
import EvmAsm.Evm64.SDiv.Layout
import EvmAsm.Evm64.SDiv.Args
import EvmAsm.Evm64.SDiv.ArgsStackDecode
import EvmAsm.Evm64.SDiv.StackExecutionBridge
import EvmAsm.Evm64.SDiv.HandlerBridge
import EvmAsm.Evm64.SDiv.Program
import EvmAsm.Evm64.SDiv.LimbSpec
import EvmAsm.Evm64.SDiv.AddrNorm
import EvmAsm.Evm64.SDiv.Compose.Base
import EvmAsm.Evm64.SDiv.Compose.Bridges
import EvmAsm.Evm64.SDiv.Compose.BaseDividendAbsBlockSpec
import EvmAsm.Evm64.SDiv.Compose.BaseDivisorAbsBlockSpec
import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs
import EvmAsm.Evm64.SDiv.Compose.DivisorAbsSequence
import EvmAsm.Evm64.SDiv.Compose.SignXorSequence
import EvmAsm.Evm64.SDiv.Compose.DivCall
import EvmAsm.Evm64.SDiv.Compose.SignFrame
import EvmAsm.Evm64.SDiv.Compose.Words
import EvmAsm.Evm64.SDiv.Compose.DispatchStackViews
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
import EvmAsm.Evm64.SDiv.Compose.DispatchViews
import EvmAsm.Evm64.SDiv.Compose.BzeroPost
import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
import EvmAsm.Evm64.SDiv.Compose.DispatchPrefix
import EvmAsm.Evm64.SDiv.Compose.BzeroCallable
import EvmAsm.Evm64.SDiv.Compose.BzeroCallableNamedPost
import EvmAsm.Evm64.SDiv.Compose.BzeroResultSignFix
import EvmAsm.Evm64.SDiv.Compose.BzeroReturn
import EvmAsm.Evm64.SDiv.Compose.BzeroReturnNormalizedView
import EvmAsm.Evm64.SDiv.Compose.BzeroReturnZeroWordView
import EvmAsm.Evm64.SDiv.Compose.BzeroReturnZeroWordRestView
import EvmAsm.Evm64.SDiv.Compose.BzeroReturnStackZeroView
import EvmAsm.Evm64.SDiv.Compose.BzeroStackViews
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatch
import EvmAsm.Evm64.SDiv.Compose.DivCallCallableReturnPost
import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixPost
import EvmAsm.Evm64.SDiv.Compose.DivCallReturnPosts
import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFix
import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixNamedPost
import EvmAsm.Evm64.SDiv.Compose.DivCallAbsComponents
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchPcFreeBasics
import EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFreeBasics
import EvmAsm.Evm64.SDiv.Compose.DivCallExactCallable
import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
import EvmAsm.Evm64.SDiv.Compose.DivCallExactCallableV5
import EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoffV5
import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5
import EvmAsm.Evm64.SDiv.Compose.PrefixChainV5
import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable
import EvmAsm.Evm64.SDiv.Compose.DivCallExactHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallN1V4Handoff
import EvmAsm.Evm64.SDiv.Compose.DivCallBzeroHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallBzeroCallableHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallExactResultSignFixHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallBzeroResultSignFixHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallExactReturnHandoff
import EvmAsm.Evm64.SDiv.Compose.DivCallBzeroReturnHandoff
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixPCFree
import EvmAsm.Evm64.SDiv.Compose.BzeroFramePCFree
import EvmAsm.Evm64.SDiv.Compose.DivCallPostPcFree
import EvmAsm.Evm64.SDiv.Compose.BzeroSemanticViews
import EvmAsm.Evm64.SDiv.Compose.DivCallDispatchZeroDivisor
import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
import EvmAsm.Evm64.SDiv.Spec
import EvmAsm.Evm64.SDiv.SpecResultBranches
