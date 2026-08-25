/-
  EvmAsm.EL.CallOutputBridge

  Generic CALL-family result/output bridge for GH #114.
-/

module

public import EvmAsm.Evm64.CallArgs
public import EvmAsm.EL.MessageCallExecution

@[expose] public section

namespace EvmAsm.EL

namespace CallOutputBridge

abbrev MemoryRange := EvmAsm.Evm64.CallArgs.MemoryRange

end CallOutputBridge

end EvmAsm.EL
