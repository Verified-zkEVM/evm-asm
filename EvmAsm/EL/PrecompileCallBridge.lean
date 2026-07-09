/-
  EvmAsm.EL.PrecompileCallBridge

  Pure bridge from EVM precompile dispatch results to CALL-family
  caller-visible result and stack framing.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.EL.CallStackBridge
import EvmAsm.EL.MessageCallExecution
import EvmAsm.Evm64.PrecompileDispatch

namespace EvmAsm.EL

namespace PrecompileCallBridge

abbrev PrecompileResult := EvmAsm.Evm64.PrecompileResult
abbrev PrecompileInput := EvmAsm.Evm64.PrecompileInput
abbrev PrecompileStatus := EvmAsm.Evm64.PrecompileStatus

end PrecompileCallBridge

end EvmAsm.EL
