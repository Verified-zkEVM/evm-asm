/-
  EvmAsm.EL.CallOutputArgsMemory

  CALL-family output-memory bridge specialized to stack argument records (GH #114).
-/

import EvmAsm.EL.CallOutputMemory
import EvmAsm.EL.CallArgsBridge

namespace EvmAsm.EL

namespace CallOutputArgsMemory

abbrev CallArgs := EvmAsm.Evm64.CallArgs.Call
abbrev StaticCallArgs := EvmAsm.Evm64.CallArgs.StaticCall
abbrev DelegateCallArgs := EvmAsm.Evm64.CallArgs.DelegateCall
abbrev Byte := EvmAsm.EL.Byte

end CallOutputArgsMemory

end EvmAsm.EL
