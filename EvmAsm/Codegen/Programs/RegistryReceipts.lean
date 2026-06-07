/- EvmAsm.Codegen.Programs.RegistryReceipts
  Receipt-related codegen registry arms.
-/
import EvmAsm.Rv64.Program
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
  | "zisk_bloom_eq" => some ziskBloomEqProbeUnit
  | "zisk_rlp_encode_u64" => some ziskRlpEncodeU64ProbeUnit
  | "zisk_receipt_encode" => some ziskReceiptEncodeProbeUnit
  | "zisk_typed_receipt_encode" => some ziskTypedReceiptEncodeProbeUnit
  | "zisk_receipt_records_probe" => some ziskReceiptRecordsProbeUnit
  | "zisk_block_receipt_records_materialize" => some ziskBlockReceiptRecordsMaterializeProbeUnit
  | "zisk_eip7778_remaining_block_gas_check" => some ziskEip7778RemainingBlockGasCheckProbeUnit
  | "zisk_block_validate_receipts_root_indexed" => some ziskBlockValidateReceiptsRootIndexedProbeUnit
  | "zisk_block_validate_receipts_consensus_list" => some ziskBlockValidateReceiptsConsensusListProbeUnit
  | "zisk_block_validate_receipts_root_one_receipt" => some ziskBlockValidateReceiptsRootOneReceiptProbeUnit
  | "zisk_block_validate_receipts_root_two_receipts" => some ziskBlockValidateReceiptsRootTwoReceiptsProbeUnit
  | "zisk_header_extract_receipts_root" => some ziskHeaderExtractReceiptsRootProbeUnit
  | "zisk_chain_extract_first_last_receipts_root" => some ziskChainExtractFirstLastReceiptsRootProbeUnit
  | "zisk_block_validate_empty_receipts_root" => some ziskBlockValidateEmptyReceiptsRootProbeUnit
  | "zisk_block_logs_bloom_from_receipts_list" => some ziskBlockLogsBloomFromReceiptsListProbeUnit
  | "zisk_block_validate_logs_bloom" => some ziskBlockValidateLogsBloomProbeUnit
  | _ => none

def knownReceiptProgramNamesTail : List String :=
  ["zisk_bloom_eq",
   "zisk_rlp_encode_u64",
   "zisk_receipt_encode",
   "zisk_typed_receipt_encode",
   "zisk_receipt_records_probe",
   "zisk_eip7778_remaining_block_gas_check",
   "zisk_block_validate_receipts_root_one_receipt",
   "zisk_block_validate_receipts_root_two_receipts",
   "zisk_header_extract_receipts_root",
   "zisk_chain_extract_first_last_receipts_root",
   "zisk_block_validate_empty_receipts_root",
   "zisk_block_logs_bloom_from_receipts_list",
   "zisk_block_validate_logs_bloom"]

end EvmAsm.Codegen
