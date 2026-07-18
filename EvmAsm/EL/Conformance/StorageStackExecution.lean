/-
  EvmAsm.EL.Conformance.StorageStackExecution

  Lean-side conformance vectors for the SLOAD/SSTORE stack execution bridge
  (GH #110 / GH #125).
-/

import EvmAsm.EL.Conformance
import EvmAsm.EL.StorageStackExecutionBridge

namespace EvmAsm.EL
namespace Conformance
namespace StorageStackExecution

abbrev EvmWord := EvmAsm.Evm64.EvmWord
abbrev StorageKind := EvmAsm.Evm64.StorageArgs.Kind
abbrev StorageStackState :=
  EvmAsm.EL.StorageStackExecutionBridge.StorageStackState
abbrev StorageAccessList :=
  EvmAsm.EL.StorageStackExecutionBridge.StorageAccessList

deriving instance DecidableEq for
  EvmAsm.EL.StorageStackExecutionBridge.StorageStackState

end StorageStackExecution
end Conformance
end EvmAsm.EL
