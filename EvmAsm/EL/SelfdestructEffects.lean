/-
  EvmAsm.EL.SelfdestructEffects

  Pure SELFDESTRUCT post-Cancun side-effect bridge (GH #113).
-/

import EvmAsm.EL.CallValueTransfer
import EvmAsm.EL.CreatedAccounts
import EvmAsm.EL.MessageCallExecution

namespace EvmAsm.EL

namespace SelfdestructEffects

abbrev CallSideEffects := MessageCallExecution.CallSideEffects

end SelfdestructEffects

end EvmAsm.EL
