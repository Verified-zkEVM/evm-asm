/-
  EvmAsm.Evm64.SDiv

  Umbrella for the SDIV opcode subtree (GH #90). Re-exports the
  top-level spec; downstream consumers should `import EvmAsm.Evm64.SDiv`
  and not reach into sub-modules directly.

  AddrNormAttr is imported first (per `AGENTS.md` `register_simp_attr`
  ordering rule) so the `sdiv_addr` attribute exists when later modules
  attach lemmas to it.
-/

module

public import EvmAsm.Evm64.SDiv.AddrNormAttr
public import EvmAsm.Evm64.SDiv.Args
public import EvmAsm.Evm64.SDiv.ArgsStackDecode
public import EvmAsm.Evm64.SDiv.StackExecutionBridge
public import EvmAsm.Evm64.SDiv.HandlerBridge
public import EvmAsm.Evm64.SDiv.Program
public import EvmAsm.Evm64.SDiv.LimbSpec
public import EvmAsm.Evm64.SDiv.AddrNorm
public import EvmAsm.Evm64.SDiv.Compose.Base
public import EvmAsm.Evm64.SDiv.Compose.Bridges
public import EvmAsm.Evm64.SDiv.Compose.SDivViewChainC
public import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
public import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs
public import EvmAsm.Evm64.SDiv.DispatchViewsShared
public import EvmAsm.Evm64.SDiv.Compose.SignFrame
public import EvmAsm.Evm64.SDiv.Compose.Words
public import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
public import EvmAsm.Evm64.SDiv.Compose.BzeroPost
public import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
public import EvmAsm.Evm64.SDiv.Compose.SDivViewChainB1
public import EvmAsm.Evm64.SDiv.DivCallHandoffChainShared
public import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
public import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5
public import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpecV5
public import EvmAsm.Evm64.SDiv.Compose.PrefixChainV5
public import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable
public import EvmAsm.Evm64.SDiv.DivCallExactShared
public import EvmAsm.Evm64.SDiv.Compose.SDivViewChainA
public import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
public import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnV5
public import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixV5
public import EvmAsm.Evm64.SDiv.Compose.DivCallReturnV5
public import EvmAsm.Evm64.SDiv.Compose.StackSpecV5
public import EvmAsm.Evm64.SDiv.SpecShared
meta import EvmAsm.Evm64.SDiv.AddrNormAttr
meta import EvmAsm.Evm64.SDiv.Args
meta import EvmAsm.Evm64.SDiv.ArgsStackDecode
meta import EvmAsm.Evm64.SDiv.StackExecutionBridge
meta import EvmAsm.Evm64.SDiv.HandlerBridge
meta import EvmAsm.Evm64.SDiv.Program
meta import EvmAsm.Evm64.SDiv.LimbSpec
meta import EvmAsm.Evm64.SDiv.AddrNorm
meta import EvmAsm.Evm64.SDiv.Compose.Base
meta import EvmAsm.Evm64.SDiv.Compose.Bridges
meta import EvmAsm.Evm64.SDiv.Compose.SDivViewChainC
meta import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpec
meta import EvmAsm.Evm64.SDiv.Compose.SaveRaSignBlockSpecs
meta import EvmAsm.Evm64.SDiv.DispatchViewsShared
meta import EvmAsm.Evm64.SDiv.Compose.SignFrame
meta import EvmAsm.Evm64.SDiv.Compose.Words
meta import EvmAsm.Evm64.SDiv.Compose.ResultSignFixZeroWordView
meta import EvmAsm.Evm64.SDiv.Compose.BzeroPost
meta import EvmAsm.Evm64.SDiv.Compose.DispatchReadyPost
meta import EvmAsm.Evm64.SDiv.Compose.SDivViewChainB1
meta import EvmAsm.Evm64.SDiv.DivCallHandoffChainShared
meta import EvmAsm.Evm64.SDiv.Compose.CodeHandlesV5
meta import EvmAsm.Evm64.SDiv.Compose.BaseCodeV5
meta import EvmAsm.Evm64.SDiv.Compose.BaseResultSignFixBlockSpecV5
meta import EvmAsm.Evm64.SDiv.Compose.PrefixChainV5
meta import EvmAsm.Evm64.SDiv.Compose.DivCallFramedCallable
meta import EvmAsm.Evm64.SDiv.DivCallExactShared
meta import EvmAsm.Evm64.SDiv.Compose.SDivViewChainA
meta import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwn
meta import EvmAsm.Evm64.SDiv.Compose.ResultSignFixOwnV5
meta import EvmAsm.Evm64.SDiv.Compose.DivCallResultSignFixV5
meta import EvmAsm.Evm64.SDiv.Compose.DivCallReturnV5
meta import EvmAsm.Evm64.SDiv.Compose.StackSpecV5
meta import EvmAsm.Evm64.SDiv.SpecShared
public meta import Lean.Meta.Tactic.Simp.Attr

public section
