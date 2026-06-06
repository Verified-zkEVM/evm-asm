/-
  EvmAsm.Codegen.Programs.RegistryTail

  Tail half of the CLI program lookup table. This is split from
  Programs.lean so the public registry module stays small and the
  generated match expression remains below backend nesting limits.
-/

import EvmAsm.Codegen.Programs.Imports

namespace EvmAsm.Codegen

def lookupProgramTail : String → Option BuildUnit
  | "zisk_bloom_eq" => some ziskBloomEqProbeUnit
  | "zisk_rlp_encode_u64" => some ziskRlpEncodeU64ProbeUnit
  | "zisk_receipt_encode" => some ziskReceiptEncodeProbeUnit
  | "zisk_typed_receipt_encode" => some ziskTypedReceiptEncodeProbeUnit
  | "zisk_receipt_records_probe" => some ziskReceiptRecordsProbeUnit | "zisk_block_receipt_records_materialize" => some ziskBlockReceiptRecordsMaterializeProbeUnit | "zisk_eip7778_remaining_block_gas_check" => some ziskEip7778RemainingBlockGasCheckProbeUnit | "zisk_receipt_records_encode_no_logs" => some ziskReceiptRecordsEncodeNoLogsProbeUnit | "zisk_block_verdict_tx_gas_limits" => some ziskBlockVerdictTxGasLimitsProbeUnit | "zisk_block_verdict_gas_result_arena" => some ziskBlockVerdictGasResultArenaProbeUnit
  | "zisk_single_leaf_trie_root" => some ziskSingleLeafTrieRootProbeUnit
  | "zisk_system_write_descriptors" => some ziskSystemWriteDescriptorsProbeUnit
  | "zisk_storage_access_gas" => some ziskStorageAccessGasProbeUnit
  
  
  | "zisk_bal_account_post_fields" => some ziskBalAccountPostFieldsProbeUnit
  | "zisk_bal_account_apply_post_fields" => some ziskBalAccountApplyPostFieldsProbeUnit
  | "zisk_bal_account_change_value" => some ziskBalAccountChangeValueProbeUnit
  | "zisk_bal_account_change_descriptor" => some ziskBalAccountChangeDescriptorProbeUnit
  | "zisk_bal_account_nth_descriptor" => some ziskBalAccountNthDescriptorProbeUnit
  | "zisk_bal_account_descriptor_array" => some ziskBalAccountDescriptorArrayProbeUnit
  | "zisk_bal_account_final_descriptor_array" => some ziskBalAccountFinalDescriptorArrayProbeUnit
  | "zisk_bal_account_state_root" => some ziskBalAccountStateRootProbeUnit
  | "zisk_bal_account_state_root_auto" => some ziskBalAccountStateRootAutoProbeUnit
  | "zisk_bal_account_record_array" => some ziskBalAccountRecordArrayProbeUnit | "zisk_bal_account_access_outcome_descriptors" => some ziskBalAccountAccessOutcomeDescriptorsProbeUnit | "zisk_bal_storage_access_outcome_descriptors" => some ziskBalStorageAccessOutcomeDescriptorsProbeUnit | "zisk_tx_gas_sender_bal_lookup" => some ziskTxGasSenderBalLookupProbeUnit | "zisk_tx_gas_bal_post_verify" => some ziskTxGasBalPostVerifyProbeUnit | "zisk_simple_transfer_tx_context" => some ziskSimpleTransferTxContextProbeUnit | "zisk_simple_transfer_recipient_bal_verify" => some ziskSimpleTransferRecipientBalVerifyProbeUnit | "zisk_simple_transfer_fee_recipient_bal_verify" => some ziskSimpleTransferFeeRecipientBalVerifyProbeUnit
  | "zisk_storage_root_single_slot" => some ziskStorageRootSingleSlotProbeUnit
  | "zisk_account_set_storage_root" => some ziskAccountSetStorageRootProbeUnit
  | "zisk_block_access_list_hash" => some ziskBlockAccessListHashProbeUnit
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
  | "zisk_block_validate_receipts_root_indexed" => some ziskBlockValidateReceiptsRootIndexedProbeUnit
  | "zisk_block_validate_receipts_consensus_list" => some ziskBlockValidateReceiptsConsensusListProbeUnit
  | "zisk_block_validate_receipts_root_one_receipt" => some ziskBlockValidateReceiptsRootOneReceiptProbeUnit
  | "zisk_block_validate_receipts_root_two_receipts" => some ziskBlockValidateReceiptsRootTwoReceiptsProbeUnit
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
  | "zisk_header_extract_receipts_root" => some ziskHeaderExtractReceiptsRootProbeUnit
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
  | "zisk_chain_extract_first_last_receipts_root" => some ziskChainExtractFirstLastReceiptsRootProbeUnit
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
  | "zisk_block_validate_empty_receipts_root" => some ziskBlockValidateEmptyReceiptsRootProbeUnit
  | "zisk_block_validate_empty_block" => some ziskBlockValidateEmptyBlockProbeUnit
  | "zisk_validate_empty_block_with_parent" => some ziskValidateEmptyBlockWithParentProbeUnit
  | "zisk_validate_empty_block_chain" => some ziskValidateEmptyBlockChainProbeUnit
  | "zisk_block_body_extract_tx_count" => some ziskBlockBodyExtractTxCountProbeUnit
  | "zisk_block_body_extract_withdrawal_count" => some ziskBlockBodyExtractWithdrawalCountProbeUnit
  | "zisk_block_body_summary" => some ziskBlockBodySummaryProbeUnit
  | "zisk_block_body_validate_empty" => some ziskBlockBodyValidateEmptyProbeUnit
  | "zisk_chain_body_total_tx_count" => some ziskChainBodyTotalTxCountProbeUnit
  | "zisk_chain_body_total_withdrawal_count" => some ziskChainBodyTotalWithdrawalCountProbeUnit
  | "zisk_block_logs_bloom_from_receipts_list" => some ziskBlockLogsBloomFromReceiptsListProbeUnit
  | "zisk_block_validate_logs_bloom" => some ziskBlockValidateLogsBloomProbeUnit
  | "zisk_header_root_is_empty_trie" => some ziskHeaderRootIsEmptyTrieProbeUnit
  | "zisk_calldata_byte_counts" => some ziskCalldataByteCountsProbeUnit
  | "zisk_intrinsic_gas_calldata_floor_eip7623" => some ziskIntrinsicGasCalldataFloorEip7623ProbeUnit
  
  | "zisk_intrinsic_gas_amsterdam_counts" => some ziskIntrinsicGasAmsterdamCountsProbeUnit
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
  | "zisk_header_nonce_at_block_hash" => some ziskHeaderNonceAtBlockHashProbeUnit
  | "zisk_extra_data_at_block_hash" => some ziskExtraDataAtBlockHashProbeUnit
  | "zisk_excess_blob_gas_at_block_hash" => some ziskExcessBlobGasAtBlockHashProbeUnit
  | "zisk_blob_gas_used_at_block_hash" => some ziskBlobGasUsedAtBlockHashProbeUnit
  | "zisk_blob_gas_pair_at_block_hash" => some ziskBlobGasPairAtBlockHashProbeUnit
  | "zisk_post_merge_invariants_at_block_hash" => some ziskPostMergeInvariantsAtBlockHashProbeUnit
  | "zisk_block_roots_at_block_hash" => some ziskBlockRootsAtBlockHashProbeUnit
  | "zisk_number_timestamp_pair_at_block_hash" => some ziskNumberTimestampPairAtBlockHashProbeUnit
  | "zisk_gas_pair_at_block_hash" => some ziskGasPairAtBlockHashProbeUnit
  | _                           => none


end EvmAsm.Codegen
