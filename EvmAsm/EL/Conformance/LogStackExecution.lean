/-
  EvmAsm.EL.Conformance.LogStackExecution

  Lean-side conformance vector for the LOG stack execution bridge
  (GH #112 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.LogStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace LogStackExecution

abbrev Byte := EvmAsm.EL.Byte
abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev LogKind := EvmAsm.Evm64.LogArgs.Kind
abbrev LogStackState := EvmAsm.EL.LogStackExecutionBridge.LogStackState
abbrev CallSideEffects := EvmAsm.EL.LogStackExecutionBridge.CallSideEffects
abbrev MemoryReader := EvmAsm.EL.LogStackExecutionBridge.MemoryReader

deriving instance DecidableEq for EvmAsm.EL.LogEntry
deriving instance DecidableEq for EvmAsm.EL.LogState
deriving instance DecidableEq for
  EvmAsm.EL.MessageCallExecution.CallSideEffects
deriving instance DecidableEq for
  EvmAsm.EL.LogStackExecutionBridge.LogStackState

structure LogStackInput where
  kind : LogKind
  emitter : Address
  memory : List Byte
  state : LogStackState

def readByteAt (memory : List Byte) (addr : Nat) : Byte :=
  memory.getD addr 0

def runLogStack? (input : LogStackInput) : Option LogStackState :=
  EvmAsm.EL.LogStackExecutionBridge.runLogStack?
    input.kind input.emitter (readByteAt input.memory) input.state

end LogStackExecution
end Conformance
end EvmAsm.EL
