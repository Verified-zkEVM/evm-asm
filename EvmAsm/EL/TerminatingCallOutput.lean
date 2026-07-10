/-
  EvmAsm.EL.TerminatingCallOutput

  Bridge from terminating opcode results to executable-spec-shaped
  message-call output (GH #113 / #121).
-/

import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingCallOutput

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev CallSideEffects := MessageCallExecution.CallSideEffects
abbrev MessageCallOutput := MessageCallExecution.MessageCallOutput

end TerminatingCallOutput

end EvmAsm.EL
