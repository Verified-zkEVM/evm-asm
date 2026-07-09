/-
  EvmAsm.EL.TerminatingExecutionBridge

  Executable-spec bridge from terminating opcode stack/memory inputs to
  caller-visible and message-call output surfaces (GH #113).
-/

import EvmAsm.EL.TerminatingCallOutput
import EvmAsm.EL.TerminatingCallerVisible
import EvmAsm.EL.TerminatingDataMemory

namespace EvmAsm.EL

namespace TerminatingExecutionBridge

abbrev TerminatingKind := TerminatingArgsBridge.TerminatingKind
abbrev TerminatingArgs := TerminatingArgsBridge.TerminatingArgs
abbrev MemoryReader := TerminatingDataMemory.MemoryReader

end TerminatingExecutionBridge

end EvmAsm.EL
