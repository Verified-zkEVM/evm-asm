/-
  EvmAsm.EL.CallStackExecutionBridge

  Pure stack-to-executor bridge for CALL-family opcodes (GH #114).
-/

import EvmAsm.Evm64.CallArgsStackDecode
import EvmAsm.EL.CallExecutionBridge

namespace EvmAsm.EL

namespace CallStackExecutionBridge

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev CallKind := EvmAsm.Evm64.CallArgs.Kind
abbrev MemoryReader := CallExecutionBridge.MemoryReader

end CallStackExecutionBridge

end EvmAsm.EL
