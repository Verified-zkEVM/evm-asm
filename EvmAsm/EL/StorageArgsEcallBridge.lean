/-
  EvmAsm.EL.StorageArgsEcallBridge

  Bridge from decoded SLOAD/SSTORE stack arguments to the storage ECALL
  request/result surface (GH #110).
-/

import EvmAsm.Evm64.StorageArgs
import EvmAsm.EL.StorageEcallStackBridge

namespace EvmAsm.EL

namespace StorageArgsEcallBridge

abbrev StorageAccessList := EvmAsm.Evm64.StorageAccess.StorageAccessList
abbrev SLoadArgs := EvmAsm.Evm64.StorageArgs.SLoad
abbrev SStoreArgs := EvmAsm.Evm64.StorageArgs.SStore

end StorageArgsEcallBridge

end EvmAsm.EL
