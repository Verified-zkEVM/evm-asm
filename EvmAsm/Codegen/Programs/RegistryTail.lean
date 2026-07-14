/-
  EvmAsm.Codegen.Programs.RegistryTail

  Tail half of the CLI program lookup table. This is split from
  Programs.lean so the public registry module stays small and the
  generated match expression remains below backend nesting limits.
-/

import EvmAsm.Codegen.Programs.Imports
import EvmAsm.Codegen.Programs.EvmLogHandlers
import EvmAsm.Codegen.Programs.EvmMessageCallGas
import EvmAsm.Codegen.Programs.TxRefund
import EvmAsm.Codegen.Programs.StorageMultiContract
import EvmAsm.Codegen.Programs.BalStorageChangeValues
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.ExecLogLatestValue
import EvmAsm.Codegen.Programs.SstoreRegularGas
import EvmAsm.Codegen.Programs.MemoryExpansionGas
import EvmAsm.Codegen.Programs.DynamicOpcodeGas
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.SlotTupleSequencesMatch
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsTupleSequences
import EvmAsm.Codegen.Programs.TxIntrinsicStateGas
import EvmAsm.Codegen.Programs.BalStorageMatchesExecLog
import EvmAsm.Codegen.Programs.ExecLogStorageSeed
import EvmAsm.Codegen.Programs.BalRecipientFieldEmpty
import EvmAsm.Codegen.Programs.BalStorageCoversExecLog
import EvmAsm.Codegen.Programs.SenderBalanceDebit
import EvmAsm.Codegen.Programs.BalStorageReadsExecLog
import EvmAsm.Codegen.Programs.CreateDescend
import EvmAsm.Codegen.Programs.BalAddrExecLogKey
import EvmAsm.Codegen.Programs.BalAllAccountsStorage
import EvmAsm.Codegen.Programs.BalAccountNonstorageFinals
import EvmAsm.Codegen.Programs.BalAccountNonstorageConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorage
import EvmAsm.Codegen.Programs.BalAllAccountsNonstorageCovers
import EvmAsm.Codegen.Programs.BalAccountCodeConsistent
import EvmAsm.Codegen.Programs.BalAllAccountsCode
import EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers
import EvmAsm.Codegen.Programs.ExtractDepositData
import EvmAsm.Codegen.Programs.TxGasBalPostVerifyRuntime
import EvmAsm.Codegen.Programs.CreateCodeEffectLog
import EvmAsm.Codegen.Programs.CreateDeployedCodeValid
import EvmAsm.Codegen.Programs.CreateInitcodeSizeValid
import EvmAsm.Codegen.Programs.CreateCreatorNonce
import EvmAsm.Codegen.Programs.SenderPostNonceConsistent
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.Programs.CreateRoundtrip
import EvmAsm.Codegen.Programs.CallBalanceGate
import EvmAsm.Codegen.Programs.CallValueEffect
import EvmAsm.Codegen.Programs.CallDepthLimit
import EvmAsm.Codegen.Programs.StageBlockhashM29
import EvmAsm.Codegen.Programs.ParseDepositRequests
import EvmAsm.Codegen.Programs.AssembleExecutionRequests
import EvmAsm.Codegen.Programs.MaterializeLogRecords
import EvmAsm.Codegen.Programs.DepositDerivationE2E
import EvmAsm.Codegen.Programs.SystemCallStaging
import EvmAsm.Codegen.Programs.SystemCallStoragePreload
import EvmAsm.Codegen.Programs.LogRecordsRlp
import EvmAsm.Codegen.Programs.DispatcherExecStateGas
import EvmAsm.Codegen.Programs.DispatcherTxGasSettle
import EvmAsm.Codegen.Programs.MultiTxSenderDebit
import EvmAsm.Codegen.Programs.BlockVerdictSenderCounts
import EvmAsm.Codegen.Programs.B3CoinbaseFee
import EvmAsm.Codegen.Programs.BlockVerdictRecipientCredits
import EvmAsm.Codegen.Programs.CommittedStorageSnapshot
import EvmAsm.Codegen.Programs.CommittedStorageLookup
import EvmAsm.Codegen.Programs.CommittedStorageBlockVerdictProbe
import EvmAsm.Codegen.Programs.BlockVerdictSystemStorageCapture
import EvmAsm.Codegen.Programs.SystemStorageSlotTuples
import EvmAsm.Codegen.Programs.SparseEpochProbe

namespace EvmAsm.Codegen

def lookupProgramTail : String → Option BuildUnit
  | "zisk_single_leaf_trie_root" => some ziskSingleLeafTrieRootProbeUnit
  | "zisk_system_write_descriptors" => some ziskSystemWriteDescriptorsProbeUnit
  | "zisk_storage_access_gas" => some ziskStorageAccessGasProbeUnit
  | "zisk_bal_gas_valid" => some ziskBalGasValidProbeUnit
  | "zisk_bal_section_info" => some ziskBalSectionInfoProbeUnit
  | "zisk_bal_account_post_fields" => some ziskBalAccountPostFieldsProbeUnit
  | "zisk_bal_account_apply_post_fields" => some ziskBalAccountApplyPostFieldsProbeUnit
  | "zisk_bal_account_change_value" => some ziskBalAccountChangeValueProbeUnit
  | "zisk_bal_account_change_descriptor" => some ziskBalAccountChangeDescriptorProbeUnit
  | "zisk_bal_account_nth_descriptor" => some ziskBalAccountNthDescriptorProbeUnit
  | "zisk_bal_account_descriptor_array" => some ziskBalAccountDescriptorArrayProbeUnit
  | "zisk_bal_account_final_descriptor_array" => some ziskBalAccountFinalDescriptorArrayProbeUnit
  | "zisk_bal_account_state_root" => some ziskBalAccountStateRootProbeUnit
  | "zisk_bal_account_state_root_auto" => some ziskBalAccountStateRootAutoProbeUnit
  | "zisk_bal_account_record_array" => some ziskBalAccountRecordArrayProbeUnit | "zisk_bal_account_access_outcome_descriptors" => some ziskBalAccountAccessOutcomeDescriptorsProbeUnit | "zisk_bal_storage_access_outcome_descriptors" => some ziskBalStorageAccessOutcomeDescriptorsProbeUnit | "zisk_tx_gas_sender_bal_lookup" => some ziskTxGasSenderBalLookupProbeUnit | "zisk_tx_gas_bal_post_verify" => some ziskTxGasBalPostVerifyProbeUnit | "zisk_simple_transfer_tx_context" => some ziskSimpleTransferTxContextProbeUnit | "zisk_multi_tx_nth_context" => some ziskMultiTxNthContextProbeUnit | "zisk_stage_runtime_payload_code" => some ziskStageRuntimePayloadCodeProbeUnit | "zisk_stage_runtime_payload_code_m29" => some ziskStageRuntimePayloadCodeM29ProbeUnit | "zisk_bytecode_is_self_contained" => some ziskBytecodeIsSelfContainedProbeUnit | "zisk_bal_find_account_by_address" => some ziskBalFindAccountByAddressProbeUnit | "zisk_stage_runtime_payload_code_storage" => some ziskStageRuntimePayloadCodeStorageProbeUnit | "zisk_stage_runtime_payload_code_calldata" => some ziskStageRuntimePayloadCodeCalldataProbeUnit | "zisk_stage_creation_runtime_payload" => some ziskStageCreationRuntimePayloadProbeUnit | "zisk_creation_runtime_windows" => some ziskCreationRuntimeWindowsProbeUnit | "zisk_bal_recipient_storage_keys" => some ziskBalRecipientStorageKeysProbeUnit | "zisk_stage_runtime_payload" => some ziskStageRuntimePayloadProbeUnit | "zisk_simple_transfer_recipient_bal_verify" => some ziskSimpleTransferRecipientBalVerifyProbeUnit | "zisk_simple_transfer_fee_recipient_bal_verify" => some ziskSimpleTransferFeeRecipientBalVerifyProbeUnit | "zisk_bal_txs_independent" => some ziskBalTxsIndependentProbeUnit | "zisk_frame_switch" => some ziskFrameSwitchProbeUnit | "zisk_frame_base" => some ziskFrameBaseProbeUnit | "zisk_call_descend" => some ziskCallDescendProbeUnit | "zisk_frame_return" => some ziskFrameReturnProbeUnit | "zisk_sparse_epoch_probe" => some ziskSparseEpochProbeUnit | "zisk_call_frame_descend" => some ziskCallFrameDescendProbeUnit | "zisk_call_depth_limit" => some callDepthLimitUnit | "zisk_call_roundtrip" => some callFrameRoundtripUnit | "zisk_create_roundtrip" => some createRoundtripUnit | "zisk_storage_multicontract" => some storageMultiContractUnit | "zisk_call_balance_gate" => some callBalanceGateUnit | "zisk_call_value_effect" => some callValueEffectUnit | "zisk_bal_storage_change_values" => some ziskBalStorageChangeValuesProbeUnit | "zisk_bal_storage_matches_exec_log" => some ziskBalStorageMatchesExecLogProbeUnit | "zisk_exec_log_append_storage_seed" => some ziskExecLogStorageSeedProbeUnit | "zisk_bal_recipient_field_empty" => some ziskBalRecipientFieldEmptyProbeUnit | "zisk_bal_storage_covers_exec_log" => some ziskBalStorageCoversExecLogProbeUnit | "zisk_bal_addr_to_exec_log_key" => some ziskBalAddrExecLogKeyProbeUnit | "zisk_bal_all_accounts_storage_consistent" => some ziskBalAllAccountsStorageConsistentProbeUnit | "zisk_sender_debit_from_gas" => some ziskSenderDebitFromGasProbeUnit | "zisk_multi_tx_running_sender_balance" => some ziskMultiTxRunningSenderBalanceProbeUnit | "zisk_b3_coinbase_fee_credit_sum" => some ziskB3CoinbaseFeeCreditSumProbeUnit | "zisk_b3_recipient_credit_table" => some ziskB3RecipientCreditTableProbeUnit | "zisk_bal_all_accounts_storage_consistent_skip_list" => some ziskBalAllAccountsStorageConsistentSkipListProbeUnit | "zisk_bal_all_accounts_tuple_sequences_consistent_skip_list" => some ziskBalAllAccountsTupleSequencesConsistentSkipListProbeUnit | "zisk_bal_storage_reads_in_exec_log" => some ziskBalStorageReadsExecLogProbeUnit | "zisk_create_descend" => some ziskCreateDescendProbeUnit | "zisk_extract_deposit_data" => some ziskExtractDepositDataProbeUnit | "zisk_parse_deposit_requests" => some ziskParseDepositRequestsProbeUnit | "zisk_create2_descend" => some ziskCreate2DescendProbeUnit | "zisk_call_extra_gas" => some ziskCallExtraGasProbeUnit | "zisk_set_call_env" => some ziskSetCallEnvProbeUnit | "zisk_bal_account_nonstorage_finals" => some ziskBalAccountNonstorageFinalsProbeUnit | "zisk_bal_account_nonstorage_consistent" => some ziskBalAccountNonstorageConsistentProbeUnit | "zisk_bal_all_accounts_nonstorage_consistent" => some ziskBalAllAccountsNonstorageConsistentProbeUnit | "zisk_bal_all_accounts_nonstorage_covers" => some ziskBalAllAccountsNonstorageCoversProbeUnit | "zisk_bal_account_code_consistent" => some ziskBalAccountCodeConsistentProbeUnit | "zisk_tx_gas_bal_post_verify_runtime" => some ziskTxGasBalPostVerifyRuntimeProbeUnit | "zisk_bal_slot_tuple_sequence" => some ziskBalSlotTupleSequenceProbeUnit | "zisk_exec_log_slot_tuples" => some ziskExecLogSlotTuplesProbeUnit | "zisk_slot_tuple_sequences_match" => some ziskSlotTupleSequencesMatchProbeUnit | "zisk_system_user_exec_log_slot_tuples" => some ziskSystemUserExecLogSlotTuplesProbeUnit | "zisk_account_set_storage_root" => some ziskAccountSetStorageRootProbeUnit | "zisk_create_code_effect_log" => some ziskCreateCodeEffectLogProbeUnit | "zisk_storage_root_single_slot" => some ziskStorageRootSingleSlotProbeUnit | "zisk_bal_all_accounts_code_consistent" => some ziskBalAllAccountsCodeConsistentProbeUnit | "zisk_create_deployed_code_valid" => some ziskCreateDeployedCodeValidProbeUnit | "zisk_account_tuple_sequences_consistent" => some ziskAccountTupleSequencesConsistentProbeUnit | "zisk_sender_post_nonce_consistent" => some ziskSenderPostNonceConsistentProbeUnit | "zisk_bal_all_accounts_code_covers" => some ziskBalAllAccountsCodeCoversProbeUnit | "zisk_bal_all_accounts_tuple_sequences_consistent" => some ziskBalAllAccountsTupleSequencesConsistentProbeUnit | "zisk_create_initcode_size_valid" => some ziskCreateInitcodeSizeValidProbeUnit | "zisk_create_creator_nonce_use" => some ziskCreateCreatorNonceUseProbeUnit | "zisk_nonstorage_effect_log" => some ziskNonstorageEffectLogProbeUnit | "zisk_nonstorage_effect_aggregate" => some ziskNonstorageEffectAggregateProbeUnit | "zisk_exec_log_latest_value" => some ziskExecLogLatestValueProbeUnit | "zisk_mtx_committed_snapshot_append" => some ziskCommittedStorageSnapshotProbeUnit | "zisk_mtx_committed_snapshot_upsert" => some ziskCommittedStorageSnapshotUpsertProbeUnit | "zisk_mtx_committed_chunked_snapshot_upsert" => some ziskCommittedStorageChunkedSnapshotUpsertProbeUnit | "zisk_mtx_committed_latest_value" => some ziskCommittedStorageLookupProbeUnit | "zisk_mtx_committed_chunked_latest_value" => some ziskCommittedStorageChunkedLookupProbeUnit | "zisk_mtx_committed_block_verdict_threading" => some ziskCommittedStorageBlockVerdictThreadingProbeUnit | "zisk_sstore_regular_gas" => some ziskSstoreRegularGasProbeUnit | "zisk_memory_expansion_gas" => some ziskMemoryExpansionGasProbeUnit | "zisk_dynamic_opcode_gas" => some ziskDynamicOpcodeGasProbeUnit | "zisk_assemble_execution_requests" => some ziskAssembleExecutionRequestsProbeUnit | "zisk_log_full_data_capture" => some ziskLogFullDataCaptureProbeUnit | "zisk_materialize_log_records" => some ziskMaterializeLogRecordsProbeUnit | "zisk_deposit_derivation_e2e" => some ziskDepositDerivationE2EProbeUnit | "zisk_stage_system_call_payload" => some ziskStageSystemCallPayloadProbeUnit | "zisk_stage_system_call" => some ziskStageSystemCallProbeUnit | "zisk_stage_predeploy_storage_preload" => some ziskStagePredeployStoragePreloadProbeUnit | "zisk_derive_withdrawal_requests" => some ziskDeriveWithdrawalRequestsProbeUnit | "zisk_derive_consolidation_requests" => some ziskDeriveConsolidationRequestsProbeUnit | "zisk_derive_requests_hash_e2e" => some ziskDeriveRequestsHashE2EProbeUnit | "zisk_derive_block_system_requests" => some ziskDeriveBlockSystemRequestsProbeUnit | "zisk_sstore_clear_gas_probe" => some ziskSstoreClearGasProbeUnit | "zisk_log_records_encode_rlp" => some ziskLogRecordsEncodeRlpProbeUnit | "zisk_ecrecover_precompile_probe" => some ziskEcrecoverPrecompileProbeUnit | "zisk_capture_exec_state_gas" => some ziskCaptureExecStateGasProbeUnit | "zisk_dispatcher_tx_gas_settle" => some ziskDispatcherTxGasSettleProbeUnit | "zisk_capture_system_storage_exec_rows" => some ziskCaptureSystemStorageExecRowsProbeUnit
  | "zisk_multi_tx_sequential_supported_shape" => some ziskMultiTxSequentialSupportedShapeProbeUnit
  | "zisk_block_access_list_hash" => some ziskBlockAccessListHashProbeUnit
  | "zisk_b1_sender_count_table" => some ziskB1SenderCountTableProbeUnit
  | "zisk_account_apply_storage_slot" => some ziskAccountApplyStorageSlotProbeUnit | "zisk_storage_effect_records_probe" => some ziskStorageEffectRecordsProbeUnit | "zisk_sstore_gas_refund_outcome" => some ziskSstoreGasRefundOutcomeProbeUnit
  | "zisk_mpt_leaf_node_encode" => some ziskMptLeafNodeEncodeProbeUnit
  | "zisk_mpt_node_slot_encode" => some ziskMptNodeSlotEncodeProbeUnit
  | "zisk_mpt_extension_node_encode" => some ziskMptExtensionNodeEncodeProbeUnit
  | "zisk_mpt_branch_node_encode" => some ziskMptBranchNodeEncodeProbeUnit
  | "zisk_nibbles_common_prefix_len" => some ziskNibblesCommonPrefixLenProbeUnit
  | "zisk_mpt_branch_payload_two_slots" => some ziskMptBranchPayloadTwoSlotsProbeUnit
  | "zisk_mpt_leaf_node_encode_from_nibbles" => some ziskMptLeafNodeEncodeFromNibblesProbeUnit
  | "zisk_mpt_branch_node_keccak" => some ziskMptBranchNodeKeccakProbeUnit
  | "zisk_mpt_two_leaf_root_indexed" => some ziskMptTwoLeafRootIndexedProbeUnit
  | "zisk_mpt_one_leaf_root_indexed" => some ziskMptOneLeafRootIndexedProbeUnit
  | "zisk_block_validate_transactions_root_one_tx" => some ziskBlockValidateTransactionsRootOneTxProbeUnit
  | "zisk_block_validate_withdrawals_root_one_w" => some ziskBlockValidateWithdrawalsRootOneWProbeUnit
  | "zisk_block_validate_withdrawals_root_two_w" => some ziskBlockValidateWithdrawalsRootTwoWProbeUnit
  | "zisk_block_validate_withdrawals_root_indexed" => some ziskBlockValidateWithdrawalsRootIndexedProbeUnit
  | "zisk_block_validate_transactions_root_two_tx" => some ziskBlockValidateTransactionsRootTwoTxProbeUnit
  | "zisk_block_hash_from_header" => some ziskBlockHashFromHeaderProbeUnit
  | "zisk_validate_parent_hash_link" => some ziskValidateParentHashLinkProbeUnit
  | "zisk_validate_header_pair" => some ziskValidateHeaderPairProbeUnit
  | "zisk_validate_header_chain" => some ziskValidateHeaderChainProbeUnit
  | "zisk_block_hash_array_from_chain" => some ziskBlockHashArrayFromChainProbeUnit
  | "zisk_validate_block_hash_chain_match" => some ziskValidateBlockHashChainMatchProbeUnit
  | "zisk_chain_compute_total_gas_used" => some ziskChainComputeTotalGasUsedProbeUnit
  | "zisk_chain_extract_number_range" => some ziskChainExtractNumberRangeProbeUnit
  | "zisk_header_extract_basefee" => some ziskHeaderExtractBasefeeProbeUnit
  | "zisk_chain_extract_basefee_range" => some ziskChainExtractBasefeeRangeProbeUnit
  | "zisk_chain_block_hashes_commitment" => some ziskChainBlockHashesCommitmentProbeUnit
  | "zisk_header_extract_state_root" => some ziskHeaderExtractStateRootProbeUnit
  | "zisk_validate_state_root_against_witness_node" => some ziskValidateStateRootAgainstWitnessNodeProbeUnit
  | "zisk_header_extract_parent_hash" => some ziskHeaderExtractParentHashProbeUnit
  | "zisk_header_extract_transactions_root" => some ziskHeaderExtractTransactionsRootProbeUnit
  | "zisk_header_extract_withdrawals_root" => some ziskHeaderExtractWithdrawalsRootProbeUnit
  | "zisk_header_extract_ommers_hash" => some ziskHeaderExtractOmmersHashProbeUnit
  | "zisk_header_extract_prev_randao" => some ziskHeaderExtractPrevRandaoProbeUnit
  | "zisk_header_extract_beneficiary" => some ziskHeaderExtractBeneficiaryProbeUnit
  | "zisk_block_hash_matches" => some ziskBlockHashMatchesProbeUnit
  | "zisk_header_extract_gas_used" => some ziskHeaderExtractGasUsedProbeUnit
  | "zisk_header_extract_gas_limit" => some ziskHeaderExtractGasLimitProbeUnit
  | "zisk_block_validate_block_hash_pair" => some ziskBlockValidateBlockHashPairProbeUnit
  | "zisk_block_hash_and_extract_number" => some ziskBlockHashAndExtractNumberProbeUnit
  | "zisk_blockhash_from_witness_headers" => some ziskBlockhashFromWitnessHeadersProbeUnit
  | "zisk_stage_blockhash_m29" => some ziskStageBlockhashM29ProbeUnit
  | "zisk_eip2935_blockhash_lookup" => some ziskEip2935BlockhashLookupProbeUnit
  | "zisk_eip4788_beacon_root_lookup" => some ziskEip4788BeaconRootLookupProbeUnit
  | "zisk_witness_headers_chain_validate" => some ziskWitnessHeadersChainValidateProbeUnit
  | "zisk_witness_headers_min_block_number" => some ziskWitnessHeadersMinBlockNumberProbeUnit
  | "zisk_witness_headers_max_block_number" => some ziskWitnessHeadersMaxBlockNumberProbeUnit
  | "zisk_blockhash_opcode_windowed" => some ziskBlockhashOpcodeWindowedProbeUnit
  | "zisk_parent_header_matches_witness_first" => some ziskParentHeaderMatchesWitnessFirstProbeUnit
  | "zisk_header_compute_summary_struct" => some ziskHeaderComputeSummaryStructProbeUnit
  | "zisk_header_extract_difficulty" => some ziskHeaderExtractDifficultyProbeUnit
  | "zisk_header_extract_extra_data" => some ziskHeaderExtractExtraDataProbeUnit
  | "zisk_header_extract_nonce" => some ziskHeaderExtractNonceProbeUnit
  | "zisk_header_validate_nonce_zero" => some ziskHeaderValidateNonceZeroProbeUnit
  | "zisk_header_validate_difficulty_zero" => some ziskHeaderValidateDifficultyZeroProbeUnit
  | "zisk_validate_header_post_merge_zeros" => some ziskValidateHeaderPostMergeZerosProbeUnit
  | "zisk_chain_validate_post_merge_zeros" => some ziskChainValidatePostMergeZerosProbeUnit
  | "zisk_chain_validate_full" => some ziskChainValidateFullProbeUnit
  | "zisk_chain_validate_increasing_timestamps" => some ziskChainValidateIncreasingTimestampsProbeUnit
  | "zisk_chain_validate_consecutive_numbers" => some ziskChainValidateConsecutiveNumbersProbeUnit
  | "zisk_chain_compute_total_blob_gas" => some ziskChainComputeTotalBlobGasProbeUnit
  | "zisk_header_extract_timestamp" => some ziskHeaderExtractTimestampProbeUnit
  | "zisk_header_extract_number" => some ziskHeaderExtractNumberProbeUnit
  | "zisk_account_validate_code_hash_empty" => some ziskAccountValidateCodeHashEmptyProbeUnit
  | "zisk_account_validate_storage_root_empty" => some ziskAccountValidateStorageRootEmptyProbeUnit
  | "zisk_chain_compute_max_gas_used" => some ziskChainComputeMaxGasUsedProbeUnit
  | "zisk_chain_compute_max_blob_gas_used" => some ziskChainComputeMaxBlobGasUsedProbeUnit
  | "zisk_chain_compute_min_gas_used" => some ziskChainComputeMinGasUsedProbeUnit
  | "zisk_chain_extract_timestamp_range" => some ziskChainExtractTimestampRangeProbeUnit
  | "zisk_chain_validate_gas_used_under_limit" => some ziskChainValidateGasUsedUnderLimitProbeUnit
  | "zisk_header_extract_blob_gas_used" => some ziskHeaderExtractBlobGasUsedProbeUnit
  | "zisk_account_validate_nonce_zero" => some ziskAccountValidateNonceZeroProbeUnit
  | "zisk_chain_compute_min_blob_gas_used" => some ziskChainComputeMinBlobGasUsedProbeUnit
  | "zisk_header_extract_excess_blob_gas" => some ziskHeaderExtractExcessBlobGasProbeUnit
  | "zisk_chain_extract_gas_used_range" => some ziskChainExtractGasUsedRangeProbeUnit
  | "zisk_chain_extract_blob_gas_used_range" => some ziskChainExtractBlobGasUsedRangeProbeUnit
  | "zisk_chain_extract_basefee_first_last" => some ziskChainExtractBasefeeFirstLastProbeUnit
  | "zisk_chain_compute_total_blob_count" => some ziskChainComputeTotalBlobCountProbeUnit
  | "zisk_chain_compute_total_basefee" => some ziskChainComputeTotalBasefeeProbeUnit
  | "zisk_chain_compute_max_basefee" => some ziskChainComputeMaxBasefeeProbeUnit
  | "zisk_chain_compute_min_basefee" => some ziskChainComputeMinBasefeeProbeUnit
  | "zisk_chain_compute_max_gas_limit" => some ziskChainComputeMaxGasLimitProbeUnit
  | "zisk_chain_compute_min_gas_limit" => some ziskChainComputeMinGasLimitProbeUnit
  | "zisk_chain_compute_total_gas_limit" => some ziskChainComputeTotalGasLimitProbeUnit
  | "zisk_chain_extract_gas_limit_first_last" => some ziskChainExtractGasLimitFirstLastProbeUnit
  | "zisk_chain_validate_constant_gas_limit" => some ziskChainValidateConstantGasLimitProbeUnit
  | "zisk_chain_validate_basefee_non_decreasing" => some ziskChainValidateBasefeeNonDecreasingProbeUnit
  | "zisk_chain_validate_basefee_non_increasing" => some ziskChainValidateBasefeeNonIncreasingProbeUnit
  | "zisk_chain_validate_gas_limit_non_decreasing" => some ziskChainValidateGasLimitNonDecreasingProbeUnit
  | "zisk_chain_validate_gas_limit_non_increasing" => some ziskChainValidateGasLimitNonIncreasingProbeUnit
  | "zisk_chain_extract_excess_blob_gas_first_last" => some ziskChainExtractExcessBlobGasFirstLastProbeUnit
  | "zisk_chain_compute_max_excess_blob_gas" => some ziskChainComputeMaxExcessBlobGasProbeUnit
  | "zisk_chain_compute_min_excess_blob_gas" => some ziskChainComputeMinExcessBlobGasProbeUnit
  | "zisk_chain_validate_excess_blob_gas_non_decreasing" => some ziskChainValidateExcessBlobGasNonDecreasingProbeUnit
  | "zisk_chain_validate_excess_blob_gas_non_increasing" => some ziskChainValidateExcessBlobGasNonIncreasingProbeUnit
  | "zisk_chain_compute_total_excess_blob_gas" => some ziskChainComputeTotalExcessBlobGasProbeUnit
  | "zisk_chain_validate_blob_gas_used_under_max" => some ziskChainValidateBlobGasUsedUnderMaxProbeUnit
  | "zisk_chain_validate_blob_gas_used_multiple" => some ziskChainValidateBlobGasUsedMultipleProbeUnit
  | "zisk_chain_compute_max_timestamp_gap" => some ziskChainComputeMaxTimestampGapProbeUnit
  | "zisk_chain_compute_min_timestamp_gap" => some ziskChainComputeMinTimestampGapProbeUnit
  | "zisk_header_extract_parent_beacon_block_root" => some ziskHeaderExtractParentBeaconBlockRootProbeUnit
  | "zisk_chain_extract_first_last_parent_beacon_block_root" => some ziskChainExtractFirstLastParentBeaconBlockRootProbeUnit
  | "zisk_header_extract_requests_hash" => some ziskHeaderExtractRequestsHashProbeUnit
  | "zisk_chain_extract_first_last_requests_hash" => some ziskChainExtractFirstLastRequestsHashProbeUnit
  | "zisk_chain_compute_max_blob_count" => some ziskChainComputeMaxBlobCountProbeUnit
  | "zisk_chain_compute_min_blob_count" => some ziskChainComputeMinBlobCountProbeUnit
  | "zisk_chain_validate_difficulty_zero" => some ziskChainValidateDifficultyZeroProbeUnit
  | "zisk_chain_validate_nonce_zero" => some ziskChainValidateNonceZeroProbeUnit
  | "zisk_chain_validate_ommers_hash_empty" => some ziskChainValidateOmmersHashEmptyProbeUnit
  | "zisk_chain_validate_post_merge_full" => some ziskChainValidatePostMergeFullProbeUnit
  | "zisk_chain_validate_extra_data_length" => some ziskChainValidateExtraDataLengthProbeUnit
  | "zisk_chain_compute_max_extra_data_length" => some ziskChainComputeMaxExtraDataLengthProbeUnit
  | "zisk_chain_extract_first_last_state_root" => some ziskChainExtractFirstLastStateRootProbeUnit
  | "zisk_chain_extract_first_last_block_hash" => some ziskChainExtractFirstLastBlockHashProbeUnit
  | "zisk_chain_extract_first_last_transactions_root" => some ziskChainExtractFirstLastTransactionsRootProbeUnit
  | "zisk_chain_extract_first_last_withdrawals_root" => some ziskChainExtractFirstLastWithdrawalsRootProbeUnit
  | "zisk_chain_extract_first_last_prev_randao" => some ziskChainExtractFirstLastPrevRandaoProbeUnit
  | "zisk_chain_extract_first_last_beneficiary" => some ziskChainExtractFirstLastBeneficiaryProbeUnit
  | "zisk_chain_extract_first_last_ommers_hash" => some ziskChainExtractFirstLastOmmersHashProbeUnit
  | "zisk_chain_validate_no_blob_txs" => some ziskChainValidateNoBlobTxsProbeUnit
  | "zisk_account_validate_balance_zero" => some ziskAccountValidateBalanceZeroProbeUnit
  | "zisk_block_validate_2tx_full" => some ziskBlockValidate2txFullProbeUnit
  | "zisk_block_body_extract_2tx" => some ziskBlockBodyExtract2txProbeUnit
  | "zisk_block_validate_2tx_full_with_body" => some ziskBlockValidate2txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_ommers_hash" => some ziskBlockValidateEmptyOmmersHashProbeUnit
  | "zisk_block_validate_no_withdrawals_pair" => some ziskBlockValidateNoWithdrawalsPairProbeUnit
  | "zisk_block_body_extract_1tx" => some ziskBlockBodyExtract1txProbeUnit
  | "zisk_block_validate_1tx_full" => some ziskBlockValidate1txFullProbeUnit
  | "zisk_block_validate_1tx_full_with_body" => some ziskBlockValidate1txFullWithBodyProbeUnit
  | "zisk_block_validate_empty_block" => some ziskBlockValidateEmptyBlockProbeUnit
  | "zisk_validate_empty_block_with_parent" => some ziskValidateEmptyBlockWithParentProbeUnit
  | "zisk_validate_empty_block_chain" => some ziskValidateEmptyBlockChainProbeUnit
  | "zisk_block_body_extract_tx_count" => some ziskBlockBodyExtractTxCountProbeUnit
  | "zisk_block_body_extract_withdrawal_count" => some ziskBlockBodyExtractWithdrawalCountProbeUnit
  | "zisk_block_body_summary" => some ziskBlockBodySummaryProbeUnit
  | "zisk_block_body_validate_empty" => some ziskBlockBodyValidateEmptyProbeUnit
  | "zisk_chain_body_total_tx_count" => some ziskChainBodyTotalTxCountProbeUnit
  | "zisk_chain_body_total_withdrawal_count" => some ziskChainBodyTotalWithdrawalCountProbeUnit
  | "zisk_header_root_is_empty_trie" => some ziskHeaderRootIsEmptyTrieProbeUnit
  | "zisk_calldata_byte_counts" => some ziskCalldataByteCountsProbeUnit
  | "zisk_intrinsic_gas_calldata_floor_eip7623" => some ziskIntrinsicGasCalldataFloorEip7623ProbeUnit
  
  | "zisk_intrinsic_gas_amsterdam_counts" => some ziskIntrinsicGasAmsterdamCountsProbeUnit
  | "zisk_eip8037_reservoir_split" => some ziskEip8037ReservoirSplitProbeUnit
  | "zisk_eip8037_tx_state_gas" => some ziskEip8037TxStateGasProbeUnit
  | "zisk_eip8037_tx_state_gas_net_array" => some ziskEip8037TxStateGasNetArrayProbeUnit
  | "zisk_eip8037_block_gas_used" => some ziskEip8037BlockGasUsedProbeUnit
  | "zisk_tx_intrinsic_state_gas" => some ziskTxIntrinsicStateGasProbeUnit
  | "zisk_block_verdict_tx_state_gas_array" => some ziskBlockVerdictTxStateGasArrayProbeUnit
  | "zisk_mpt_nibbles_to_compact" => some ziskMptNibblesToCompactProbeUnit
  | "zisk_mpt_compact_to_nibbles" => some ziskMptCompactToNibblesProbeUnit
  
  | "zisk_mpt_encode_internal_node" => some ziskMptEncodeInternalNodeProbeUnit
  | "zisk_mpt_branch_get_child" => some ziskMptBranchGetChildProbeUnit
  | "zisk_mpt_branch_get_value" => some ziskMptBranchGetValueProbeUnit
  
  | "zisk_mpt_extension_extract" => some ziskMptExtensionExtractProbeUnit
  | "zisk_mpt_branch_used_count" => some ziskMptBranchUsedCountProbeUnit
  | "zisk_mpt_branch_first_used_index" => some ziskMptBranchFirstUsedIndexProbeUnit
  
  
  
  
  
  
  | "zisk_ssz_hash_tree_root_bytes" => some ziskSszHashTreeRootBytesProbeUnit
  | "zisk_ssz_hash_tree_root_list_bytelist" => some ziskSszHashTreeRootListByteListProbeUnit
  | "zisk_ssz_hash_tree_root_execution_witness" => some ziskSszHashTreeRootExecutionWitnessProbeUnit
  | "zisk_ssz_pair_hash" => some ziskSszPairHashProbeUnit
  | "zisk_ssz_zero_hashes" => some ziskSszZeroHashesProbeUnit
  | "zisk_ssz_merkleize_pow2" => some ziskSszMerkleizePow2ProbeUnit
  | "zisk_ssz_merkleize" => some ziskSszMerkleizeProbeUnit
  | "zisk_ssz_pack_bytes" => some ziskSszPackBytesProbeUnit
  | "zisk_header_nonce_at_block_hash" => some ziskHeaderNonceAtBlockHashProbeUnit
  | "zisk_extra_data_at_block_hash" => some ziskExtraDataAtBlockHashProbeUnit
  | "zisk_excess_blob_gas_at_block_hash" => some ziskExcessBlobGasAtBlockHashProbeUnit
  | "zisk_blob_gas_used_at_block_hash" => some ziskBlobGasUsedAtBlockHashProbeUnit
  | "zisk_blob_gas_pair_at_block_hash" => some ziskBlobGasPairAtBlockHashProbeUnit
  | "zisk_post_merge_invariants_at_block_hash" => some ziskPostMergeInvariantsAtBlockHashProbeUnit
  | "zisk_block_roots_at_block_hash" => some ziskBlockRootsAtBlockHashProbeUnit
  | "zisk_number_timestamp_pair_at_block_hash" => some ziskNumberTimestampPairAtBlockHashProbeUnit
  | "zisk_gas_pair_at_block_hash" => some ziskGasPairAtBlockHashProbeUnit
  -- Re-register probes whose dispatch arms were dropped in a registry refactor;
  -- each still has a codegen-zisk-*-check.sh. See bead evm-asm-8bt13.
  | "zisk_bal_account_path" => some ziskBalAccountPathProbeUnit
  | "zisk_block_verdict_tx_gas_limits" => some ziskBlockVerdictTxGasLimitsProbeUnit
  | "zisk_init_code_cost" => some ziskInitCodeCostProbeUnit
  | "zisk_message_call_gas" => some ziskMessageCallGasProbeUnit
  | "zisk_mpt_leaf_extract" => some ziskMptLeafExtractProbeUnit
  | "zisk_mpt_node_classify" => some ziskMptNodeClassifyProbeUnit
  | "zisk_receipt_records_encode_no_logs" => some ziskReceiptRecordsEncodeNoLogsProbeUnit
  | "zisk_runtime_access_account_outcome_records" => some ziskRuntimeAccessAccountOutcomeRecordsProbeUnit
  | "zisk_runtime_access_seed_account_list" => some ziskRuntimeAccessSeedAccountListProbeUnit
  | "zisk_sha256_from_input" => some ziskSha256FromInputProbeUnit
  | "zisk_storage_access_outcome_records" => some ziskStorageAccessOutcomeRecordsProbeUnit
  | "zisk_storage_access_seed" => some ziskStorageAccessSeedProbeUnit
  | "zisk_tx_refund_cap" => some ziskTxRefundCapProbeUnit
  | name => lookupReceiptProgramTail name


end EvmAsm.Codegen
