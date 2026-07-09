/-
  EvmAsm.EL.TerminatingArgsBridge

  Bridge from EVM RETURN/REVERT stack arguments to EL message-call results
  (GH #113).

  Mirrors the shape of `EvmAsm.EL.LogArgsBridge` and
  `EvmAsm.EL.CallArgsBridge`: a tiny pure layer that takes the loaded data
  byte slice, the post-execution `WorldState`, and the remaining gas, and
  produces a `CallResult` with the appropriate `CallStatus` (`.success` for
  RETURN, `.revert` for REVERT). The actual memory-load / state-update work
  belongs to the eventual handler specs — this bridge just packages the
  result.
-/

import EvmAsm.EL.MessageCall
import EvmAsm.Evm64.TerminatingArgs

namespace EvmAsm.EL

namespace TerminatingArgsBridge

abbrev MemoryRange := EvmAsm.Evm64.TerminatingArgs.MemoryRange
abbrev TerminatingArgs := EvmAsm.Evm64.TerminatingArgs.Args
abbrev TerminatingKind := EvmAsm.Evm64.TerminatingArgs.Kind

/-- Memory range projected from the terminating-args record. -/
def dataRange (args : TerminatingArgs) : MemoryRange :=
  EvmAsm.Evm64.TerminatingArgs.dataRange args

end TerminatingArgsBridge

end EvmAsm.EL
