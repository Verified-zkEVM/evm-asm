/- EvmAsm.Codegen.Programs.RegistryReceipts
  Receipt-related codegen registry arms.
-/
import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.Account
import EvmAsm.Codegen.Programs.Bloom
import EvmAsm.Codegen.Programs.BlockEmpty
import EvmAsm.Codegen.Programs.BlockGasRemaining
import EvmAsm.Codegen.Programs.BlockRoots
import EvmAsm.Codegen.Programs.BlockVerdictReceiptRecords
import EvmAsm.Codegen.Programs.ChainEndpoints
import EvmAsm.Codegen.Programs.HeaderFields
import EvmAsm.Codegen.Programs.Receipt
import EvmAsm.Codegen.Programs.ReceiptRecords
import EvmAsm.Codegen.Programs.ReceiptsConsensus
import EvmAsm.Codegen.Programs.ReceiptsRootIndexed

namespace EvmAsm.Codegen

def lookupReceiptProgramTail : String → Option BuildUnit

  | _ => none

def knownReceiptProgramNamesTail : List String :=
  [

   ]

end EvmAsm.Codegen
