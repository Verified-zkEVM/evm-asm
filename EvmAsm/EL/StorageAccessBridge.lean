/-
  EvmAsm.EL.StorageAccessBridge

  Bridge from the pure EL SLOAD/SSTORE semantics to the Evm64 cold/warm
  storage-access outcome surface (GH #110).  This is still pure data:
  later ECALL and stack-level opcode specs can consume these records to
  connect handler execution to the executable storage model.

  Authored by @pirapira; implemented by Codex.
-/

import EvmAsm.Evm64.StorageAccessOutcome

namespace EvmAsm.EL
namespace StorageAccessBridge

end StorageAccessBridge
end EvmAsm.EL
