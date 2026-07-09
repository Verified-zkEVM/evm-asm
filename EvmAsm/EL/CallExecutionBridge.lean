/-
  EvmAsm.EL.CallExecutionBridge

  CALL-family execution input bridge from stack-decoded arguments to the
  message-call executor surface (GH #114).
-/

import EvmAsm.EL.CallInputBridge
import EvmAsm.EL.CallResultEffectsBridge

namespace EvmAsm.EL

namespace CallExecutionBridge

abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall
abbrev MemoryReader := CallInputBridge.MemoryReader

end CallExecutionBridge

end EvmAsm.EL
