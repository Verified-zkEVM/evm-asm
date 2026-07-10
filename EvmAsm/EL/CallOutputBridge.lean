/-
  EvmAsm.EL.CallOutputBridge

  Generic CALL-family result/output bridge for GH #114.
-/

import EvmAsm.Evm64.CallArgs
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace CallOutputBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange

end CallOutputBridge

end EvmAsm.EL
