/-
  EvmAsm.EL.TerminatingCallerVisible

  Bridge from terminating opcode results to the executable-spec caller-visible
  message-call result surface (GH #113 / #121).
-/

import EvmAsm.EL.MessageCallExecution
import EvmAsm.EL.TerminatingArgsBridge

namespace EvmAsm.EL

namespace TerminatingCallerVisible

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs

/-- Caller-visible output selected by a terminating opcode result. RETURN and
    REVERT propagate their memory slice; STOP, INVALID, and SELFDESTRUCT expose
    empty output. -/
def propagatedTerminatingOutput (kind : TerminatingKind) (data : List Byte) :
    List Byte :=
  match kind with
  | .stop => []
  | .return_ => data
  | .revert => data
  | .invalid => []
  | .selfdestruct => []

end TerminatingCallerVisible

end EvmAsm.EL
