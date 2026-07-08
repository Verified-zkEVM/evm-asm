/-
  EvmAsm.Codegen.Programs.BlockVerdictDataSection

  Data-section (BSS/static arenas) for the stateless verdict v2 program.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard
import EvmAsm.Codegen.Programs.LogRecordsRlp
import EvmAsm.Codegen.Programs.TxPubkey
import EvmAsm.Codegen.Programs.VerifyPublicKeysSenders
import EvmAsm.Codegen.Programs.BalStorageMatchesExecLog
import EvmAsm.Codegen.Programs.BalStorageCoversExecLog
import EvmAsm.Codegen.Programs.BalAllAccountsStorage
import EvmAsm.Codegen.Programs.BalAllAccountsCodeCovers
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.BalStorageReadsExecLog
import EvmAsm.Codegen.Programs.BlockVerdictSenderCounts

namespace EvmAsm.Codegen

def ziskStatelessVerdictV2DataSection : String :=
  -- .62.2.5: secp256k1 recovery scratch/constants for the ECRECOVER backend
  -- (generator + field constants + R-decompression scratch + tpr_* recovery
  -- scratch). Emitted first so the additions cannot disturb existing label
  -- ordering assumptions below.
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  -- bmvmx.3.2: TX-side sender-recovery scratch (signature material + per-type
  -- extractor offsets + signing-hash buffers) + verify_public_keys_match_senders
  -- scratch + bv_chain_id. The secp/tpr_* recovery data above is already present
  -- for the ECRECOVER backend; this adds only the transaction-signature delta.
  verifyPublicKeysSendersGuestDataSection ++ "\n" ++
  ziskStatelessVerdictDataSection ++ "\n" ++
  runtimeAccessAccountOutcomeData ++ "\n" ++
  storageAccessGasData ++ "\n" ++
  executionRequestsHashDataSection ++ "\n" ++
  ".balign 32\n" ++
  "svf_tx_root:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "svf_bal_hash:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "svf_withdrawals_root:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "bv_block_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bv_block_hash_check_enabled:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "svf_tx_count:\n  .zero 8\n" ++
  "svf_tx_descriptors:\n  .zero 32768\n" ++
  "bah_bal_start:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "sltr_field_len:\n  .zero 8\n" ++
  "sltr_nibble_count:\n  .zero 8\n" ++
  "sltr_hp_len:\n  .zero 8\n" ++
  "sltr_cursor:\n  .zero 8\n" ++
  "sltr_total_payload:\n  .zero 8\n" ++
  "sltr_nibbles:\n  .zero 2048\n" ++
  "sltr_hp_buf:\n  .zero 1024\n" ++
  "sltr_payload_buf:\n  .zero 16384\n" ++
  "sltr_node_buf:\n  .zero 16384\n" ++
  "mtoli_nibbles:\n  .zero 8\n" ++
  "mtoli_leaf_len:\n  .zero 8\n" ++
  "mtoli_leaf_buf:\n  .zero 16384\n" ++
  ".balign 32\n" ++
  "srss_key:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "srss_rlpval:\n  .zero 40\n" ++
  "srss_rlpval_len:\n  .zero 8\n" ++
  "asr_ref:\n  .zero 40\n" ++
  "aps_off:\n  .zero 8\n" ++
  "aps_len:\n  .zero 8\n" ++
  "aps_witness_ptr:\n  .zero 8\n" ++
  "aps_witness_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aps_newsroot:\n  .zero 32\n" ++
  "aps_path:\n  .zero 64\n" ++
  "aps_empty_root:\n" ++
  "  .byte 0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6\n" ++
  "  .byte 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e\n" ++
  "  .byte 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0\n" ++
  "  .byte 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21\n" ++
  ".balign 32\n" ++
  "swd_2935_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_2935_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_val:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_slot:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "swd_4788_root_val:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "swd_2935_vlen:\n  .zero 8\n" ++
  "swd_4788_vlen:\n  .zero 8\n" ++
  "swd_4788_root_vlen:\n  .zero 8\n" ++
  "bv_eip4788_current_fast_seen:\n  .zero 8\n" ++
  "swd_ts_be8:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bsr_root_p:\n  .zero 8\n" ++
  "bsr_wit_p:\n  .zero 8\n" ++
  "bsr_wl_v:\n  .zero 8\n" ++
  "bsr_ssz_p:\n  .zero 8\n" ++
  "bsr_bal_start:\n  .zero 8\n" ++
  "bsr_bal_len:\n  .zero 8\n" ++
  "bsr_bal_count:\n  .zero 8\n" ++
  "bsr_exec_p:\n  .zero 8\n" ++
  "bsr_tx_off:\n  .zero 8\n" ++
  "bsr_pathp:\n  .zero 8\n" ++
  "bsr_acct_len:\n  .zero 8\n" ++
  "bsr_tmplen:\n  .zero 8\n" ++
  "bsr_prev_desc:\n  .zero 8\n" ++
  "bsr_prev_acct:\n  .zero 8\n" ++ ziskBalAccountHasStateChangeDataSection ++
  "bsr_bal_item_ptr:\n  .zero 8\n" ++
  "bsr_bal_item_len:\n  .zero 8\n" ++
  ziskBalAccountIsModeledSystemDataSection ++
  ".balign 32\n" ++
  "bsr_kbuf:\n  .zero 32\n" ++
  "bsr_delta:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsr_acct:\n  .zero 256\n" ++
  "bsr_paths:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrPathBytes) ++
  "\nbsr_newaccts:\n  .zero " ++ toString (bsrMaxAuxChanges * bsrSystemAccountBytes) ++
  "\nbsr_changes:\n  .zero " ++ toString (bsrMaxStateChanges * bsrStateChangeBytes) ++ "\n" ++
  "bsr_changed_account_count:\n  .zero 8\n" ++
  "bsr_access_count:\n  .zero 8\n" ++
  "bsr_storage_access_path_count:\n  .zero 8\n" ++
  "bsr_storage_access_window:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "bsr_changed_accounts:\n  .zero " ++ toString (bsrMaxAccessAccounts * 32) ++ "\n" ++
  "bsr_access_paths:\n  .zero " ++ toString (bsrMaxAccountAccessOutcomes * bsrPathBytes) ++ "\n" ++
  "bsr_storage_account_token:\n  .zero " ++ toString (bsrMaxAccessAccounts * 32) ++ "\n" ++
  "bsr_storage_access_paths:\n  .zero " ++ toString (bsrMaxStorageAccessOutcomes * bsrPathBytes) ++ "\n" ++
  "baaod_hash:\n  .zero 32\n" ++
  "bsaod_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bsaod_empty_value:\n  .zero 1\n" ++
  "baaod_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 32\n" ++
  "bsr_addr_2935:\n" ++
  "  .byte 0x00, 0x00, 0xF9, 0x08, 0x27, 0xF1, 0xC5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7A, 0x02, 0x33, 0x5B, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  ".balign 32\n" ++
  "bsr_addr_4788:\n" ++
  "  .byte 0x00, 0x0F, 0x3d, 0xf6, 0xD7, 0x32, 0x80, 0x7E\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xB7, 0xB8, 0xbB, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xBe, 0xac, 0x02\n" ++
  ".balign 8\n" ++
  "bgv_count:\n  .zero 8\n" ++
  "bgv_off:\n  .zero 8\n" ++
  "bgv_size:\n  .zero 8\n" ++
  "bgv_acctlen:\n  .zero 8\n" ++
  "bv_exec_p:\n  .zero 8\n" ++
  "bv_npr_p:\n  .zero 8\n" ++
  "bv_bal_start:\n  .zero 8\n" ++
  "bv_bal_len:\n  .zero 8\n" ++
  "bv_tx_off:\n  .zero 8\n" ++
  "bv_tx_list_ptr:\n  .zero 8\nbv_tx_list_len:\n  .zero 8\nbv_tx_count:\n  .zero 8\nbv_tx_index:\n  .zero 8\nbv_tx_item_start:\n  .zero 8\n" ++
  "bv_public_keys_ptr:\n  .zero 8\n" ++
  "bv_public_keys_len:\n  .zero 8\n" ++
  "bv_fail_code:\n  .zero 8\n" ++
  "bv_header_status:\n  .zero 8\n" ++
  "bv_state_status:\n  .zero 8\n" ++
  "bv_tx_root_status:\n  .zero 8\n" ++
  "bv_block_rlp_len:\n  .zero 8\n" ++
  "bv_blockhash_required_headers:\n  .zero 8\n" ++
  "bv_versioned_hashes_len:\n  .zero 8\n" ++
  "bv_blob_gas_expected:\n  .zero 8\n" ++
  "bv_blob_gas_observed:\n  .zero 8\n" ++
  "bv_withdrawals_root_status:\n  .zero 8\n" ++
  "bv_withdrawals_root_valid:\n  .zero 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  -- .63.1.6.2.1: per-tx execution-status plumbing. bv_tx_status_arr holds the
  -- dispatcher_tx_gas_settle success bit per tx (single-tx path writes index 0,
  -- the mtx loop index i); brr_tx_status_ptr is the materializer's saved arg.
  "brr_tx_status_ptr:\n  .zero 8\n" ++
  "bv_tx_status_arr:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.2: per-tx creation-error refund eligibility flag parallel to
  -- bv_tx_status_arr, used by the EIP-8037 tx-error state-gas rule when
  -- materializing exact block state gas.
  "bv_tx_is_creation_arr:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- .63.1.6.2.1: block-level log arena + per-tx windows. Each dispatch call
  -- resets/overwrites the capture buffers, so block_log_window_snapshot copies
  -- every tx's descriptors (256 B each, 128 cap) + data bytes (64 KiB cap,
  -- offsets rebased into bv_block_log_meta) out between dispatches.
  -- bv_record_* and bv_logs_rlp_arena carry the per-record logs RLP + blooms
  -- (block_receipt_logs_materialize), in the {bloom,rlp,len} shape
  -- receipt_records_encode_no_logs consumes via record@56.
  "brr_tx_window_ptr:\n  .zero 8\n" ++
  "bv_block_log_count:\n  .zero 8\n" ++
  "bv_block_log_data_used:\n  .zero 8\n" ++
  "bv_block_log_desc_used:\n  .zero 8\n" ++
  "bv_block_log_overflow:\n  .zero 8\n" ++
  "bv_last_log_start:\n  .zero 8\n" ++
  "bv_last_log_count:\n  .zero 8\n" ++
  "bv_receipt_logs_status:\n  .zero 8\n" ++
  "bv_logs_rlp_len:\n  .zero 8\n" ++
  "bv_logs_rlp_arena_used:\n  .zero 8\n" ++
  "bv_tx_log_window:\n  .zero " ++ toString bvMtxLogWindowBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_block_log_descs:\n  .zero " ++ toString bvBlockLogDescBytes ++ "\n" ++
  "bv_block_log_meta:\n  .zero " ++ toString bvBlockLogMetaBytes ++ "\n" ++
  "bv_block_log_data:\n  .zero " ++ toString bvBlockLogDataBytes ++ "\n" ++
  "bv_logs_rlp_arena:\n  .zero " ++ toString bvLogsRlpArenaBytes ++ "\n" ++
  "bv_record_blooms:\n  .zero " ++ toString bvRecordBloomsBytes ++ "\n" ++
  "bv_record_logs_desc:\n  .zero " ++ toString bvRecordLogsDescBytes ++ "\n" ++
  -- .63.1.6.2.3: encoded full-receipt RLP list plus encoder scratch.
  -- Output/scratch overflow is capacity debt and remains conservative unless a
  -- later slice proves a supported in-capacity semantic mismatch.
  "bv_receipts_rlp:\n  .zero " ++ toString bvReceiptsRlpBytes ++ "\n" ++
  "bv_receipts_rlp_len:\n  .zero 8\n" ++
  -- Status returned by receipt_records_encode_no_logs in the receipts tail:
  -- 0 success, 1 malformed/count over capacity, 2 missing logs descriptor,
  -- 3 output/scratch overflow, 4 unsupported tx type.
  "bv_receipts_encoder_status:\n  .zero 8\n" ++
  -- Status returned by block_validate_receipts_consensus_list in the receipts tail:
  -- 0 success, 1 receipts-root helper failure, 2 receipts-root mismatch,
  -- 3 logs-bloom helper failure, 4 logs-bloom mismatch.
  "bv_receipts_validator_status:\n  .zero 8\n" ++
  -- .63.1.6.2.3: receipt_encode + receipt_records_encode_no_logs scratch (these labels were
  -- probe-only in ziskReceiptRecordsEncodeNoLogsDataSection before the tx-bearing un-gate linked
  -- the encoder into the guest). re_payload_buf / rle_payload_buf are the per-receipt
  -- and list payload scratch; rle_empty_logs/rle_zero_bloom are the no-log receipt constants.
  ".balign 8\n" ++
  "rle_control:\n  .zero 24\n" ++
  "rle_records:\n  .zero " ++ toString bvReceiptRecordsBytes ++ "\n" ++
  "rle_field_len:\n  .zero 8\n" ++
  "rle_prefix_len:\n  .zero 8\n" ++
  "re_field_len:\n  .zero 8\n" ++
  "re_cursor:\n  .zero 8\n" ++
  "re_total_payload:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "rle_empty_logs:\n  .byte 0xc0\n" ++
  ".balign 8\n" ++
  "rle_zero_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "re_payload_buf:\n  .zero " ++ toString bvReceiptEncodePayloadBytes ++ "\n" ++
  ".balign 8\n" ++
  "rle_payload_buf:\n  .zero " ++ toString bvReceiptListPayloadBytes ++ "\n" ++
  -- .63.1.6.2.3: block_validate_logs_bloom + block_logs_bloom_from_receipts_list scratch
  -- (helb_offset/helb_length are already linked via header_extract_logs_bloom).
  ".balign 8\n" ++
  "relb_offset:\n  .zero 8\n" ++
  "relb_length:\n  .zero 8\n" ++
  "blbr_count:\n  .zero 8\n" ++
  "blbr_offset:\n  .zero 8\n" ++
  "blbr_length:\n  .zero 8\n" ++
  "blbr_next_offset:\n  .zero 8\n" ++
  "blbr_next_length:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "blbr_scratch_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bvlb_header_bloom:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bvlb_computed_bloom:\n  .zero 256\n" ++
  -- .63.1.6.2.3: block_validate_receipts_consensus_list scratch (the indexed-trie/root and
  -- logs-bloom sub-scratch are already linked above / via the no-tx receipts path).
  ".balign 8\n" ++
  "brcl_count:\n  .zero 8\n" ++
  "brcl_offset:\n  .zero 8\n" ++
  "brcl_length:\n  .zero 8\n" ++
  "brcl_next_offset:\n  .zero 8\n" ++
  "brcl_next_length:\n  .zero 8\n" ++
  "brcl_root_valid:\n  .zero 8\n" ++
  "brcl_bloom_valid:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "brcl_value_descs:\n  .zero " ++ toString bvReceiptConsensusDescBytes ++ "\n" ++
  -- scratch for log_records_encode_rlp (lrr_*) and the bloom accumulators
  -- (bav_/lba_/llba_ — zk3_state is already defined by the guest).
  logRecordsRlpDataSection ++
  "bav_hash:\n  .zero 32\n" ++
  "lba_offset:\n  .zero 8\n" ++
  "lba_length:\n  .zero 8\n" ++
  "lba_topics_offset:\n  .zero 8\n" ++
  "lba_topics_length:\n  .zero 8\n" ++
  "lba_topic_count:\n  .zero 8\n" ++
  "llba_offset:\n  .zero 8\n" ++
  "llba_length:\n  .zero 8\n" ++
  "llba_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero " ++ toString bvReceiptRecordsBytes ++ "\n" ++
  "hewr_offset:\n  .zero 8\n" ++
  "hewr_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bvwri_expected_root:\n  .zero 32\n" ++
  "bvwri_computed_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "itr_empty_witness:\n  .zero 8\n" ++
  "itr_value_descs:\n  .zero 32768\n" ++
  "itr_paths:\n  .zero 16384\n" ++
  "itr_changes:\n  .zero 81920\n" ++
  -- .63.1.6.2.3: receipts-consensus scratch (mirrors the hewr_/bvwri_ withdrawals
  -- pair above). herr_/helb_ are header field-extraction cursors; bvrri_* the
  -- expected/computed receipts roots + per-receipt {ptr,len} descriptors (16 B ×
  -- 128, same cap as mpt_indexed_trie_root_small); bv_header_bloom /
  -- bv_zero_bloom / bv_bloom_eq_out drive the header.logs_bloom compare.
  "herr_offset:\n  .zero 8\n" ++
  "herr_length:\n  .zero 8\n" ++
  "helb_offset:\n  .zero 8\n" ++
  "helb_length:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bvrri_expected_root:\n  .zero 32\n" ++
  "bvrri_computed_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bvrri_value_descs:\n  .zero " ++ toString bvReceiptConsensusDescBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_header_bloom:\n  .zero 256\n" ++
  "bv_zero_bloom:\n  .zero 256\n" ++
  "bv_bloom_eq_out:\n  .zero 8\n" ++
  "bvgr_runtime_gas_left_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_refund_counter_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_calldata_floor_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_count:\n  .zero 8\n" ++
  ".balign 8\n" ++
  -- bmvmx.1.7.2: sized to fit a max EIP-170 contract (round8(24576)) + 128-slot storage
  -- preload (128*64=8192) + the 584-byte env/gas trailer + headroom for calldata and the
  -- future M29 blockhash table (.3b). dispatch_tx_runtime_code's .Ldtrc_stage guard bails
  -- conservatively for any payload that would still exceed this, so the staging write can
  -- never overflow into the adjacent gas-result / bvcd_* cells.
  "bv_runtime_payload:\n  .zero " ++ toString (bsrAccountSlotCap * 64 + 65536) ++ "\n" ++   -- 4jczt class-B BAL>128 lift: hold storage*64 at the gas-derived bsrAccountSlotCap (6.4MB) + the original 65536 code/calldata/witness/584 headroom (calldata/witness worst case stays bmvmx.1.7.2's payload-cap concern). .data headroom verified ~61MB (dataBase 0xa3000000 -> sszScratchBase 0xbf500000).
  "bv_stop_code:\n  .byte 0x00\n" ++
  ".balign 8\n" ++
  "bv_runtime_gas_left:\n  .zero 8\n" ++
  "bv_runtime_refund_counter:\n  .zero 8\n" ++
  "bv_runtime_calldata_floor:\n  .zero 8\n" ++
  "bv_runtime_intrinsic_state_gas:\n  .zero 8\n" ++
  -- Last dispatch_tx_runtime_code status: 0 success; 1 code lookup; 2 non-self-contained;
  -- 3 BAL/account/key cap; 4 storage proof/slot lookup; 5 payload cap; 6 staging;
  -- 7 access-list unsupported/parse/count. Nonzero still means conservative bail.
  "bv_dispatch_runtime_status:\n  .zero 8\n" ++
  -- Runtime-gas completeness classifier: 0 complete/unknown, 1 gas-result arena tx/count/cap,
  -- 2 runtime_count/pointer mismatch, 3 single-tx dispatch unsupported,
  -- 4 multi-tx dispatch unsupported, 5 multi-tx generic bail. Nonzero is debug-only.
  "bv_runtime_completeness_status:\n  .zero 8\n" ++
  -- Contract-recipient dispatch scratch (evm-asm-fhsxz.2.4.2.57.11.6.4.3.2).
  ".balign 8\n" ++
  "bvcd_code_ptr:\n  .zero 8\n" ++
  "bvcd_code_len:\n  .zero 8\n" ++
  "bvcd_acct_ptr:\n  .zero 8\n" ++
  "bvcd_acct_len:\n  .zero 8\n" ++
  "bvcd_key_count:\n  .zero 8\n" ++
  "bvcd_sc_count:\n  .zero 8\n" ++
  "bvcd_i:\n  .zero 8\n" ++
  "bvcd_keys:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++     -- .66.1.2: bsrAccountSlotCap x 32-byte slot keys (bal_recipient_storage_keys caps at the gas-derived bsrAccountSlotCap; the dispatch-tx caller still bails >128 — bvcd_preload stays 128-sized — but the keys the helper writes before that bail must fit)
  "bvcd_preload:\n  .zero " ++ toString (bsrAccountSlotCap * 64) ++ "\n" ++   -- 4jczt class-B BAL>128 lift: bsrAccountSlotCap x 64-byte (key,value) pairs, matching bvcd_keys (was 128*64=8192). The dispatch-tx caller no longer bails >128 storage slots.
  -- bmvmx.1.6.2 exec-vs-BAL recipient storage check scratch (bal_storage_change_values +
  -- bal_storage_matches_exec_log), now linked into the verdict's contract-dispatch tail.
  balStorageChangeValuesData ++
  balStorageMatchesExecLogData ++
  -- bmvmx.1.6.5 exec ⊆ BAL omission-detection scratch (bal_storage_covers_exec_log).
  balStorageCoversExecLogData ++
  -- bmvmx.1.6.4.3 all-accounts storage check scratch (bal_all_accounts_storage_consistent, c2bal_*).
  balAllAccountsStorageConsistentData ++
  -- i3djw all-accounts CODE reverse scratch (bal_all_accounts_code_covers, bacov_*).
  balAllAccountsCodeCoversData ++
  -- bmvmx.1.6.7 storage_reads exec-consistency scratch.
  balStorageReadsInExecLogData ++
  -- bmvmx.1.6.3 recipient nonce/code-change emptiness probe (rlp_list_nth_item out cells).
  "bv_rcf_off:\n  .zero 8\n" ++
  "bv_rcf_len:\n  .zero 8\n" ++
  -- bmvmx.1.6.4.2.b seed_callee_storage scratch: BAL-account + slot loop state, the
  -- per-account LE exec-log key, and the callee storage-key buffer (own buffer so it
  -- can't overflow the recipient's 16-slot bvcd_keys; caps with the 128-entry table).
  ".balign 8\n" ++
  "csce_acct_i:\n  .zero 8\n" ++ "csce_acct_n:\n  .zero 8\n" ++
  "csce_aoff:\n  .zero 8\n" ++ "csce_alen:\n  .zero 8\n" ++
  "csce_doff:\n  .zero 8\n" ++ "csce_dlen:\n  .zero 8\n" ++
  "csce_addrp:\n  .zero 8\n" ++
  "csce_key_i:\n  .zero 8\n" ++ "csce_key_n:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "csce_addrkey:\n  .zero 32\n" ++
  "csce_keys:\n  .zero " ++ toString (bsrAccountSlotCap * 32) ++ "\n" ++   -- .66.1.2: bsrAccountSlotCap x 32-byte slot keys (matches the gas-derived bal_recipient_storage_keys cap; the seed loop still skips accounts >128)
  -- 1ipxd.1: pre-resolved per-account balance table for nested-frame SELFBALANCE.
  -- seed_callee_storage fills it (clean pre-execution context, where the witness MPT walk
  -- works — it returns absent mid-EVM-execution); call_frame_descend reads it to stage a
  -- child frame's env+32. Entry = 64 B: canonical-BE 20-byte address (zero-padded to 32) @0,
  -- balance @32 in LE-limb (stack-word) order so the descend copies it verbatim to the LE
  -- EVM stack via h_SELFBALANCE (odq06 byte-order lesson). 128 cap. csce_bal_struct = the
  -- account_at_header_state_root output (nonce@0 / balance@8..40 BE / sroot / codehash).
  ".balign 8\n" ++
  "csce_bal_struct:\n  .zero 104\n" ++
  "callee_balance_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "callee_balance_table:\n  .zero " ++ toString (512 * 64) ++ "\n" ++

  "bv_eip7778_status:\n  .zero 8\n" ++
  "bv_eip7778_index:\n  .zero 8\n" ++
  "bv_eip7778_used:\n  .zero 8\n" ++
  "bvgr_status:\n  .zero 8\n" ++
  "bvgr_count:\n  .zero 8\n" ++
  "bvgr_fail_index:\n  .zero 8\n" ++
  "bvgr_tx_type:\n  .zero 8\n" ++
  "bvgr_tx_inner:\n  .zero 8\n" ++
  "bvgr_nonce:\n  .zero 8\n" ++
  "bvgr_gas:\n  .zero 8\n" ++
  "bvgr_arena_status:\n  .zero 8\n" ++
  "bvgr_arena_tx_count:\n  .zero 8\n" ++
  "bvgr_arena_runtime_count:\n  .zero 8\n" ++
  "bvgr_arena_fail_index:\n  .zero 8\n" ++
  "bvgr_arena_substatus:\n  .zero 8\n" ++
  "bvgr_tx_gas_limits:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_gas_left:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_refund_counter:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_calldata_floor:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_block_gas_increments:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- g8zeq.1.4.3: per-tx EIP-8037 state-gas array, the state counterpart of
  -- bvgr_block_gas_increments. Filled by block_verdict_tx_state_gas_array; fed
  -- (with bvgr_block_gas_increments) to eip8037_block_gas_used by g8zeq.1.4.2.
  "bvgr_tx_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: per-tx EXECUTED state gas (net of refunds), filled by
  -- dispatcher_capture_exec_state_gas at each contract dispatch (mirrors
  -- bvgr_tx_state_gas). Behavior-neutral substrate for the 2D state-dim (P3 reads it).
  "bvgr_tx_exec_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.1: exact net EIP-8037 tx_state_gas = intrinsic + executed - refund,
  -- with transaction error rules applied. Populated after runtime gas results.
  "bvgr_tx_total_state_gas:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- xbi56.2: EIP-8037 state-refund input to the net state-gas materializer.
  -- Current block-verdict runtime paths do not yet expose nonzero state refunds;
  -- this zero-initialized array keeps the exact block gas check honest for rows
  -- with no state refund and leaves refund plumbing as explicit follow-up debt.
  "bvgr_tx_state_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- Per-tx count of EIP-7702 authorities whose pre-state code was already a
  -- delegation marker. Those authorities are warm for the receipt regular
  -- dimension, so the type-4 auth regular delta is discounted by 2600 each.
  "bvgr_tx_predelegated_auth_count:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_exact_header_gas_used:\n  .zero 8\n" ++
  "bv_exact_expected_gas_used:\n  .zero 8\n" ++
  "bv_exact_net_status:\n  .zero 8\n" ++
  "bv_exact_net_index:\n  .zero 8\n" ++
  "bv_exact_block_status:\n  .zero 8\n" ++
  "bvgr_receipt_gas_increments:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_before_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bvgr_applied_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  -- EIP-7702 state-refund scratch used by tx_eip7702_existing_authority_refund.
  -- The current helper is a coarse syntactic bridge; evm-asm-cqesh tracks the
  -- precise BAL/account predicate follow-up.
  "teer_type:\n  .zero 8\n" ++
  "teer_inner_off:\n  .zero 8\n" ++
  "teer_auth_off:\n  .zero 8\n" ++
  "teer_auth_len:\n  .zero 8\n" ++
  "teer_auth_count:\n  .zero 8\n" ++
  "teer_predelegated_count:\n  .zero 8\n" ++
  "teer_records_ptr:\n  .zero 8\n" ++
  "teer_tuple_off:\n  .zero 8\n" ++
  "teer_tuple_len:\n  .zero 8\n" ++
  "teer_target_off:\n  .zero 8\n" ++
  "teer_target_len:\n  .zero 8\n" ++
  "teer_auth_chain:\n  .zero 8\n" ++
  "teer_auth_nonce:\n  .zero 8\n" ++
  "teer_first_nonce:\n  .zero 8\n" ++
  "teer_authority:\n  .zero 24\n" ++
  "teer_first_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "teer_recover_scratch:\n  .zero 360\n" ++
  "teer_acct_ptr:\n  .zero 8\n" ++
  "teer_acct_len:\n  .zero 8\n" ++
  "teer_finals:\n  .zero 88\n" ++
  "teer_pre_acct:\n  .zero 104\n" ++
  -- coc3g.5 multi-hop: eip7702_warm_recovered_authorities private scratch.
  ".balign 8\n" ++
  "e77w_count:\n  .zero 8\n" ++
  "e77w_toff:\n  .zero 8\n" ++
  "e77w_tlen:\n  .zero 8\n" ++
  "e77w_chain:\n  .zero 8\n" ++
  "e77w_nonce:\n  .zero 8\n" ++
  "e77w_authority:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "e77w_scratch:\n  .zero 360\n" ++
  "a77ra_cmp:\n  .zero 8\n" ++
  "a77ra_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "a77ra_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
  "ta77es_offset:\n  .zero 8\n" ++
  "ta77es_length:\n  .zero 8\n" ++
  "bvrga_type:\n  .zero 8\n" ++
  "bvrga_inner_off:\n  .zero 8\n" ++
  "bvrga_auth_off:\n  .zero 8\n" ++
  "bvrga_auth_len:\n  .zero 8\n" ++
  "bvrga_auth_count:\n  .zero 8\n" ++
  blockVerdictTxGasPrechargeDataSection ++
  ".balign 8\n" ++
  -- uyu11.1: EIP-4895 withdrawal-aware credit scratch for the coinbase/recipient
  -- post-balance checks + the bv_sum_withdrawals_to_address accumulator.
  "strv_wd_credit:\n  .zero 32\n" ++
  "stfv_wd_credit:\n  .zero 32\n" ++
  "bsw_amount:\n  .zero 32\n" ++
  "bsw_wei:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "strv_count:\n  .zero 8\n" ++
  "strv_row_off:\n  .zero 8\n" ++
  "strv_row_len:\n  .zero 8\n" ++
  "strv_addr_off:\n  .zero 8\n" ++
  "strv_addr_len:\n  .zero 8\n" ++
  "strv_post_len:\n  .zero 8\n" ++
  "strv_nonce_len:\n  .zero 8\n" ++
  "stfv_count:\n  .zero 8\n" ++
  "stfv_row_off:\n  .zero 8\n" ++
  "stfv_row_len:\n  .zero 8\n" ++
  "stfv_addr_off:\n  .zero 8\n" ++
  "stfv_addr_len:\n  .zero 8\n" ++
  "stfv_post_len:\n  .zero 8\n" ++
  "stfv_nonce_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "strv_post_raw:\n  .zero 32\n" ++
  "strv_nonce_raw:\n  .zero 32\n" ++
  "stfv_effective_gas_price:\n  .zero 32\n" ++
  "stfv_post_raw:\n  .zero 32\n" ++
  "stfv_nonce_raw:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bv_simple_transfer_recipient:\n  .zero 208\n" ++
  "bv_simple_transfer_fee_recipient:\n  .zero 240\n" ++
  ".balign 8\n" ++
  "tvhm_tx_type:\n  .zero 8\n" ++
  "tvhm_inner_off:\n  .zero 8\n" ++
  "tvhm_blob_count:\n  .zero 8\n" ++
  "tvhm_blob_index:\n  .zero 8\n" ++
  "tvhm_hash_off:\n  .zero 8\n" ++
  "tvhm_hash_len:\n  .zero 8\n" ++
  "tvhm_struct:\n  .zero 248\n" ++
  eip7702NonceReuseGuardDataSection ++
  "brl_item_start:\n  .zero 8\n" ++
  "brl_item_end:\n  .zero 8\n" ++
  "brl_wd_len:\n  .zero 8\n" ++
  "brl_wd_buf:\n  .zero 72\n" ++
  "svf_witness_section:\n  .zero 8\n" ++
  "svf_witness_end:\n  .zero 8\n" ++
  "svf_codes_ptr:\n  .zero 8\n" ++
  "svf_codes_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "wclh_scratch_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "svf_headers_ptr:\n  .zero 8\n" ++
  "svf_headers_len:\n  .zero 8\n" ++
  -- 8uld3.2.3.3.1 (C.1): scratch for execution-derived withdrawal+consolidation requests_hash.
  ".balign 8\n" ++
  "c1_saved_logcount:\n  .zero 8\n" ++
  "c1_system_log_cursor:\n  .zero 8\n" ++
  -- bmvmx.5.5.1.2.1.3.1.1: side arena for system-call SSTORE rows.
  -- The system-call derives append to the regular storage log, then the verdict
  -- restores evm_env+448 so user storage/nonstorage comparators preserve their
  -- current behavior. Capture those erased rows here with txindex=0 for the
  -- follow-up tuple-merge comparator.
  "bv_system_storage_log_count:\n  .zero 8\n" ++
  "bv_system_storage_txindex:\n  .zero " ++ toString bvSystemStorageTxindexBytes ++ "\n" ++
  -- 4ch8f.73: bv_system_storage_log is a STANDALONE .data region (NOT unioned into
  -- call_frame_arena). The former ~77 MiB union placement was UNSOUND: the audit's
  -- claimed "dead during Phase-D dispatch" was false — the syslog is WRITTEN
  -- pre-dispatch (capture_system_storage_exec_rows) but READ POST-dispatch by the
  -- BAL validators (bal_storage_matches_exec_log @BlockVerdictFunction:972,
  -- bal_storage_covers_exec_log :984, account_tuple_sequences_consistent :1135),
  -- while per-tx dispatch frames at depth ≥ 221 physically zero the union front
  -- (call_frame_arena + (d-1)*0x39000 covers the syslog extent). Reservation was
  -- also tightened from the unreachable gas bound (600000 rows) to
  -- bvSystemStorageLogCapacity (= 2 * runtime exec-log cap 16384; see
  -- BlockVerdictParams) so the standalone region is only 4 MiB and fits the .data
  -- headroom. Disjointness from every frame slot: syslog_disjoint_from_frameArena
  -- (RegionMap.lean).
  ".balign 32\n" ++
  "bv_system_storage_log:\n  .zero " ++ toString bvSystemStorageLogBytes ++ "\n" ++
  ".balign 8\n" ++
  "bv_system_storage_capture_status:\n  .zero 8\n" ++
  "bv_system_storage_capture_start:\n  .zero 8\n" ++
  "bv_system_storage_capture_end:\n  .zero 8\n" ++
  "bv_system_storage_capture_rows:\n  .zero 8\n" ++
  "bv_system_storage_capture_old_count:\n  .zero 8\n" ++
  "bv_system_storage_capture_new_count:\n  .zero 8\n" ++
  "cssc_stamp_txindex:\n  .zero 8\n" ++       -- lv44p.2.2: block_access_index stamped into captured system rows
  "c1_wcode_ptr:\n  .zero 8\n" ++
  "c1_wcode_len:\n  .zero 8\n" ++
  "c1_er_input:\n  .zero 8\n" ++
  ".balign 8\n" ++
  -- Fix7: system-call payload = env_base+504; env_base grows with the predeploy's storage preload (up to 128 slots*64) + M29 block hashes. 4096 overflowed for above-max queues (100 slots -> ~7.5KB) -> truncated storage section -> SLOAD miss -> empty derived body.
  -- fhsxz.2.4.2.66.1: 32768 overflowed for the system_contract_errors EEST predeploys
  -- (modified 7002/7251 contracts of 72946 B; predeploy code is NOT EIP-170-bounded):
  -- stage_runtime_payload_code's zero+code copy ran ~40 KiB past the buffer, smashing
  -- every .data global above (c1_saved_*, dbsr_*, rlp args) -> ERROR(exit)/false-reject.
  -- .66.1.2: sized by the shared c1StagingBytes constant (BlockVerdictParams.lean) =
  -- bsrMaxWitnessBytes + bsrAccountSlotCap*64 + 16384 — fits round8(code <= witness cap)
  -- + the gas-derived preload + M29 + 584. The size guard in stage_system_call_payload
  -- (SystemCallStaging.lean) uses the same constant and bails on anything larger
  -- instead of corrupting .data.
  "c1_staging:\n  .zero " ++ toString c1StagingBytes ++ "\n" ++
  ".balign 8\n" ++
  "c1_er_assembled:\n  .zero " ++ toString bvMaxExecutionRequestSectionBytes ++ "\n" ++
  "c1_er_assembled_len:\n  .zero 8\n" ++
  "c1_erh_status:\n  .zero 8\n" ++
  "c1_notx_deposit_body_len:\n  .zero 8\n" ++
  "c1_dstatus:\n  .zero 8\n" ++
  "c1_dlen:\n  .zero 8\n" ++
  "c1_dbody:\n  .zero " ++ toString bvMaxDepositRequestBodyBytes ++ "\n" ++
  "c1_log_records:\n  .zero " ++ toString bvMaxDepositLogRecordBytes ++ "\n" ++
  "c1_ccode_ptr:\n  .zero 8\n" ++
  "c1_ccode_len:\n  .zero 8\n" ++
  "c1_bal_acct_ptr:\n  .zero 8\n" ++
  "c1_bal_acct_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "c1_preload:\n  .zero " ++ toString (bsrAccountSlotCap * 64) ++ "\n" ++   -- .66.1.2: bsrAccountSlotCap x 64-byte (key,value) pairs — gas-derived (a 200M block's user txs can legitimately put up to the whole BAL budget of changes+reads on a predeploy; the former 512 false-rejected those blocks)
  "c1_bal_start:\n  .zero 8\n" ++
  "c1_bal_len:\n  .zero 8\n" ++
  "c1_bal_count:\n  .zero 8\n" ++
  "c1_saved_s0:\n  .zero 8\n" ++
  "c1_saved_s3:\n  .zero 8\n" ++
  "svf_headers_count:\n  .zero 8\n" ++
  "bbcv_count:\n  .zero 8\n" ++
  "bbcv_off:\n  .zero 8\n" ++
  "bbcv_size:\n  .zero 8\n" ++
  "bbcv_acct_len:\n  .zero 8\n" ++
  "bbcv_addr_off:\n  .zero 8\n" ++
  "bbcv_addr_len:\n  .zero 8\n" ++
  "bbcv_acct_struct:\n  .zero 104\n" ++
  "aahsr_state_root:\n  .zero 32\n" ++
  "bbcv_field_off:\n  .zero 8\n" ++
  "bbcv_field_len:\n  .zero 8\n" ++
  "bbcv_field_count:\n  .zero 8\n" ++
  "bbcv_balance_count:\n  .zero 8\n" ++
  "bbcv_nonce_count:\n  .zero 8\n" ++
  "bbcv_skip_touch_only:\n  .zero 8\n" ++
  "bbcv_touch_only:\n  .zero 8\n" ++
  "bbcv_fee_recipient_valid:\n  .zero 8\n.balign 8\nbbcv_fee_recipient:\n  .zero 20\n" ++
  ".balign 32\n" ++
  "bbcv_sys_2935:\n" ++
  "  .byte 0x00, 0x00, 0xf9, 0x08, 0x27, 0xf1, 0xc5, 0x3a\n" ++
  "  .byte 0x10, 0xcb, 0x7a, 0x02, 0x33, 0x5b, 0x17, 0x53\n" ++
  "  .byte 0x20, 0x00, 0x29, 0x35\n" ++
  "bbcv_sys_4788:\n" ++
  "  .byte 0x00, 0x0f, 0x3d, 0xf6, 0xd7, 0x32, 0x80, 0x7e\n" ++
  "  .byte 0xf1, 0x31, 0x9f, 0xb7, 0xb8, 0xbb, 0x85, 0x22\n" ++
  "  .byte 0xd0, 0xbe, 0xac, 0x02\n" ++
  "bbcv_sys_7002:\n" ++
  "  .byte 0x00, 0x00, 0x09, 0x61, 0xef, 0x48, 0x0e, 0xb5\n" ++
  "  .byte 0x5e, 0x80, 0xd1, 0x9a, 0xd8, 0x35, 0x79, 0xa6\n" ++
  "  .byte 0x4c, 0x00, 0x70, 0x02\n" ++
  "bbcv_sys_7251:\n" ++
  "  .byte 0x00, 0x00, 0xbb, 0xdd, 0xc7, 0xce, 0x48, 0x86\n" ++
  "  .byte 0x42, 0xfb, 0x57, 0x9f, 0x8b, 0x00, 0xf3, 0xa5\n" ++
  "  .byte 0x90, 0x00, 0x72, 0x51\n" ++
  "bbcv_sys_6110:\n" ++
  "  .byte 0x00, 0x00, 0x00, 0x00, 0x21, 0x9a, 0xb5, 0x40\n" ++
  "  .byte 0x35, 0x6c, 0xbb, 0x83, 0x9c, 0xbe, 0x05, 0x30\n" ++
  "  .byte 0x3d, 0x77, 0x05, 0xfa\n" ++
  "bbcv_sys_system:\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff\n" ++
  "  .byte 0xff, 0xff, 0xff, 0xfe\n" ++
  ".balign 32\n" ++
  "bbcv_code_hash:\n  .zero 32\n" ++
  "bbcv_delegated_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bbcv_code_off:\n  .zero 8\n" ++
  "bbcv_code_len:\n  .zero 8\n" ++
  "bbcv_scan_count:\n  .zero 8\n" ++
  "bbcv_scan_off:\n  .zero 8\n" ++
  "bbcv_scan_size:\n  .zero 8\n" ++
  "bbcv_scan_addr_off:\n  .zero 8\n" ++
  "bbcv_scan_addr_len:\n  .zero 8\n" ++
  "bv_cf_code_off:\n  .zero 8\n" ++
  "bv_cf_code_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_tx_recipient_code_hash:\n  .zero 32\n" ++
  "bv_create_addr:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bv_creation_ctx_ptr:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bbcv_sender_addr:\n  .zero 32\n" ++
  "bbcv_create_addr:\n  .zero 32\n" ++
  "bbcv_create2_salt:\n  .zero 32\n" ++
  "ac2_inner_digest:\n  .zero 32\n" ++
  "ac2_outer_digest:\n  .zero 32\n" ++
  "ac2_preimage:\n  .zero 88\n" ++
  "ac_buffer:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ac_nonce_be:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "ac_digest:\n  .zero 32\n" ++
  "bbcv_stop_code_hash:\n" ++
  "  .quad 0x14281e7a9e7836bc, 0x7d818f8229424636, 0x9165d677b4f71266, 0x8ac9bc64e0a996ff\n" ++
  "chahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "chahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "chahsr_empty_code_hash:\n" ++
  "  .quad 0x3c23f7860146d2c5, 0xc003c7dcb27d7e92, 0x3b2782ca53b600e5, 0x70a4855d04d8fa7b\n" ++
  "ad_offset:\n  .zero 8\n" ++
  "ad_length:\n  .zero 8\n" ++
  "aa_value_len:\n  .zero 8\n" ++
  "ecsahsr_dummy_offset:\n  .zero 8\n" ++
  "ecsahsr_code_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "aa_value_scratch:\n  .zero 256\n" ++
  "ecsahsr_state_root:\n  .zero 32\n" ++
  "mlk_keccak_buf:\n  .zero 32\n" ++
  "mlk_nibble_buf:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ecsahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "ecsahsr_empty_code_hash:\n" ++
  "  .byte 0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c\n" ++
  "  .byte 0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0\n" ++
  "  .byte 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b\n" ++
  "  .byte 0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70\n" ++
  ".balign 32\n" ++
  "vh_keccak_table:\n" ++
  "  .zero 8192\n" ++
  ".balign 32\n" ++
  "vh_extracted_parent_hash:\n" ++
  "  .zero 32\n" ++
  "bsg_count:\n  .zero 8\n" ++
  "bsg_off:\n  .zero 8\n" ++
  "bsg_len:\n  .zero 8\n" ++
  "bsg_tx_nonce:\n  .zero 8\n" ++
  "bsg_slot_count:\n  .zero 8\n" ++
  "bsg_slot_off:\n  .zero 8\n" ++
  "bsg_slot_len:\n  .zero 8\n" ++
  "bsg_slot_ptr:\n  .zero 8\n" ++
  "bsg_slot_item_len:\n  .zero 8\n" ++
  "bsg_changes_off:\n  .zero 8\n" ++
  "bsg_changes_len:\n  .zero 8\n" ++
  "bsg_changes_ptr:\n  .zero 8\n" ++
  "bsg_change_count:\n  .zero 8\n" ++
  "bsg_change_off:\n  .zero 8\n" ++
  "bsg_change_len:\n  .zero 8\n" ++
  "bsg_change_ptr:\n  .zero 8\n" ++
  "bsg_change_item_len:\n  .zero 8\n" ++
  "bsg_idx_off:\n  .zero 8\n" ++
  "bsg_idx_len:\n  .zero 8\n" ++
  "bsg_index:\n  .zero 8\n" ++
  "bsg_value_off:\n  .zero 8\n" ++
  "bsg_value_len:\n  .zero 8\n" ++
  "bsg_tx_type:\n  .zero 8\n" ++
  "bsg_tx_inner:\n  .zero 8\n" ++
  "bsg_tx_gas:\n  .zero 8\n" ++
  "bsg_gas_field:\n  .zero 8\n" ++
  "bsg_to_field:\n  .zero 8\n" ++
  "bsg_data_field:\n  .zero 8\n" ++
  "bsg_access_field:\n  .zero 8\n" ++
  "bsg_auth_field:\n  .zero 8\n" ++
  "bsg_intrinsic_gas:\n  .zero 8\n" ++
  "bsg_floor_gas:\n  .zero 8\n" ++
  "bsg_data_ptr:\n  .zero 8\n" ++
  "bsg_data_off:\n  .zero 8\n" ++
  "bsg_data_len:\n  .zero 8\n" ++
  "bsg_to_off:\n  .zero 8\n" ++
  "bsg_to_len:\n  .zero 8\n" ++
  "bsg_access_off:\n  .zero 8\n" ++
  "bsg_access_len:\n  .zero 8\n" ++
  "bsg_access_addrs:\n  .zero 8\n" ++
  "bsg_access_slots:\n  .zero 8\n" ++
  "bsg_auth_off:\n  .zero 8\n" ++
  "bsg_auth_len:\n  .zero 8\n" ++
  "bsg_auth_count:\n  .zero 8\n" ++
  "bsg_min_block_gas:\n  .zero 8\n" ++
  "alc_scratch:\n  .zero 8\n" ++
  "alc_entry_offset:\n  .zero 8\n" ++
  "alc_entry_length:\n  .zero 8\n" ++
  "alc_keys_offset:\n  .zero 8\n" ++
  "alc_keys_length:\n  .zero 8\n" ++
  "bsg_worst_state:\n  .zero 8\n" ++
  "bsg_prior_state:\n  .zero 8\n" ++
  "bsg_state_gas:\n  .zero 8\n" ++
  "bsg_exact_state_ok:\n  .zero 8\n" ++
  "bsg_blob_count:\n  .zero 8\n" ++
  "bsg_blob_gas_accum:\n  .zero 8\n" ++
  "bgvh_count_scratch:\n  .zero 8\n" ++
  "tcbg_struct:\n  .zero 248\n" ++
  -- Full u256 (BE) max_fee_per_blob_gas, persisted by tx_eip4844_decode for
  -- callers that need the >u64 value (EIP-8037 gate blob-price check). tcbg_struct+160
  -- keeps only the low-64 view; in the high blob-fee regime (excess_blob_gas > ~328M)
  -- the price and a valid tx's max_fee both exceed u64, so the gate compares u256.
  "tcbg_blob_fee_be:\n  .zero 32\n" ++
  "bsg_blob_price_be:\n  .zero 32\n" ++
  "bsg_blob_lt_out:\n  .zero 8\n" ++
  "bsr_fail_code:\n  .zero 8\n" ++
  "bsr_change_count:\n  .zero 8\n" ++
  "sri_cur_mode:\n  .zero 8\n" ++
  "sri_fail_index:\n  .zero 8\n" ++
  "sri_fail_mode:\n  .zero 8\n" ++
  "sri_fail_status:\n  .zero 8\n" ++
  "bpf_list_off:\n  .zero 8\n" ++
  "bpf_list_len:\n  .zero 8\n" ++
  "bpf_list_ptr:\n  .zero 8\n" ++
  "bpf_count:\n  .zero 8\n" ++
  "bpf_item_off:\n  .zero 8\n" ++
  "bpf_item_len:\n  .zero 8\n" ++
  "bpf_item_ptr:\n  .zero 8\n" ++
  "bpf_val_off:\n  .zero 8\n" ++
  "bpf_val_len:\n  .zero 8\n" ++
  "baap_bal_len:\n  .zero 8\n" ++
  "baap_nonce_len:\n  .zero 8\n" ++
  "baap_tmp_len:\n  .zero 8\n" ++
  "baap_tmp2_len:\n  .zero 8\n" ++
  "baap_fail_code:\n  .zero 8\n" ++
  "baap_sc_off:\n  .zero 8\n" ++
  "baap_sc_len:\n  .zero 8\n" ++
  "baap_sc_ptr:\n  .zero 8\n" ++
  "baap_sc_count:\n  .zero 8\n" ++
  "baap_sc_index:\n  .zero 8\n" ++
  "baap_sc_out_count:\n  .zero 8\n" ++
  "baap_storage_empty_flag:\n  .zero 8\n" ++
  "baap_force_storage_clear:\n  .zero 8\n" ++
  "baap_storage_delete_flag:\n  .zero 8\n" ++
  "baap_storage_delete_count:\n  .zero 8\n" ++
  "baap_storage_delete_index:\n  .zero 8\n" ++
  "baap_storage_root_ptr:\n  .zero 8\n" ++
  "baap_walk_val_len:\n  .zero 8\n" ++
  "mdacc_witness_len:\n  .zero 8\n" ++
  "mdacc_survivor_nibble:\n  .zero 8\n" ++
  "mdacc_child_ptr:\n  .zero 8\n" ++
  "mdacc_child_len:\n  .zero 8\n" ++
  "mdacc_leaf_path_len:\n  .zero 8\n" ++
  "mdacc_ext_path_len:\n  .zero 8\n" ++
  "mdacc_leaf_value_ptr:\n  .zero 8\n" ++
  "mdacc_leaf_value_len:\n  .zero 8\n" ++
  "mee_path_off:\n  .zero 8\n" ++
  "mee_path_len:\n  .zero 8\n" ++
  "baap_item_off:\n  .zero 8\n" ++
  "baap_item_len:\n  .zero 8\n" ++
  "baap_slot_changes_off:\n  .zero 8\n" ++
  "baap_slot_changes_len:\n  .zero 8\n" ++
  "baap_slot_changes_ptr:\n  .zero 8\n" ++
  "baap_slot_changes_count:\n  .zero 8\n" ++
  "baap_val_off:\n  .zero 8\n" ++
  "baap_val_len:\n  .zero 8\n" ++
  "baap_val_ptr:\n  .zero 8\n" ++
  "baap_code_list_off:\n  .zero 8\n" ++
  "baap_code_list_len:\n  .zero 8\n" ++
  "baap_code_list_ptr:\n  .zero 8\n" ++
  "baap_code_count:\n  .zero 8\n" ++
  "baap_code_item_ptr:\n  .zero 8\n" ++
  "baap_code_off:\n  .zero 8\n" ++
  "baap_code_len:\n  .zero 8\n" ++
  "baap_tmp3_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "baap_bal:\n  .zero 32\n" ++
  "baap_nonce:\n  .zero 32\n" ++
  "baap_slot:\n  .zero 32\n" ++
  "baap_code_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baap_tmp:\n  .zero 512\n" ++
  "baap_tmp2:\n  .zero 512\n" ++
  "baap_tmp3:\n  .zero 512\n" ++
  "baap_storage_value_cursor:\n  .zero 8\n" ++
  "baap_walk_val:\n  .zero 128\n" ++
  -- a1vvy step 3: baap_storage_desc/paths/delete_paths/values (~22 MiB) are
  -- UNIONED into call_frame_arena (emitted below) to free the last .data headroom
  -- for the vv4hr.3.4.2 full log-arena lift. They are Phase-H-only (referenced only
  -- in BalAccountApplyPostFields / BlockVerdictSysChange / BlockVerdictStateRoot --
  -- BAL post-field apply + system-change application within the state-root
  -- recompute) and dead during Phase-D dispatch when call_frame_arena is live.
  "mdacc_leaf_path:\n  .zero 128\n" ++
  "mdacc_collapsed_path:\n  .zero 128\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baacd_value_len:\n  .zero 8\n" ++
  "baacd_is_empty:\n  .zero 8\n" ++
  "baacd_fail_code:\n  .zero 8\n" ++
  "aie_offset:\n  .zero 8\n" ++
  "aie_length:\n  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  "bacv_fail_code:\n  .zero 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "basr_records:\n  .zero " ++ toString (bsrMaxStateChanges * bsrAccountRecordBytes) ++
  "\nbasr_paths:\n  .zero " ++ toString (bsrMaxStateChanges * bsrPathBytes) ++
  -- a1vvy (2026-06-18): REINSTATED #8513 union to reclaim ~49 MiB of .data
  -- headroom for the 200M log/receipt capacity lifts (vv4hr.3.4.*). basr_values +
  -- basr_accounts are block_state_root replay scratch, referenced ONLY in
  -- BalAccountStateRoot/BlockVerdictStateRoot (Phase H: pre-dispatch state-root
  -- recompute) and dead from the first tx dispatch onward (#8513 gate-verified:
  -- no post-replay reader; re-confirmed 2026-06-18 — no Phase D/T reference).
  -- call_frame_arena is referenced ONLY by CallFrameBase/Descend/Return (Phase D
  -- dispatch). The phases are sequential with disjoint live windows, so the frame
  -- array reuses the basr pair's space as a union. The size relation FLIPPED vs
  -- #8513 (frame ~165 MiB > basr pair ~49 MiB at the 200M capacity), so instead of
  -- the arena aliasing INTO the pair, the pair is coalesced into the FRONT of
  -- call_frame_arena (both labels point inside the arena; the trailing .zero pads
  -- to the full frameArrayBytes). basr_values/basr_accounts are reached via
  -- independent `la`, so relocation is transparent; they stay 32-aligned and keep
  -- their original contiguous delta. Fit + non-overlap pinned by
  -- `frameArray_unions_basr_pair` (CallFrameLayout.lean); ELF ground truth =
  -- readelf -lW top RW LOAD < 0xc0000000.
  "\n.balign 32\n" ++
  "call_frame_arena:\n" ++
  "basr_values:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  "\nbasr_accounts:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  -- 4ch8f.73: bv_system_storage_log is NO LONGER unioned here (it is read
  -- post-dispatch, so a frame slot would clobber it). The four baap_storage_*
  -- arenas remain unioned (Phase-H, block_state_root-only, 32-aligned).
  "\nbaap_storage_desc:\n  .zero " ++ toString (bsrMaxBalItems * baapStorageDescBytes) ++
  "\nbaap_storage_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++
  "\nbaap_storage_delete_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++
  "\nbaap_storage_values:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++
  "\n  .zero " ++ toString (frameArrayBytes - 2 * (bsrMaxStateChanges * bsrEncodedAccountBytes) - (bsrMaxBalItems * baapStorageDescBytes) - 3 * (bsrMaxBalItems * bsrPathBytes)) ++
  "\ncall_frame_arena_end:\n" ++ "\n" ++
  ".balign 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  ".balign 8\n" ++
  "bsr_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "iw_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  ".balign 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ins_wl:\n  .zero 8\n" ++
  "ins_node_len:\n  .zero 8\n" ++
  "ins_ref_len:\n  .zero 8\n" ++
  "mle_path_off:\n  .zero 8\n" ++
  "mle_path_len:\n  .zero 8\n" ++
  "ins_kcount:\n  .zero 8\n" ++
  "ins_lv_ptr:\n  .zero 8\n" ++
  "ins_lv_len:\n  .zero 8\n" ++
  "ins_m:\n  .zero 8\n" ++
  "ins_niba:\n  .zero 8\n" ++
  "ins_nibb:\n  .zero 8\n" ++
  "ins_node2_len:\n  .zero 8\n" ++
  "ins_ref2_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "ins_meta:\n  .zero 48\n" ++
  ".balign 8\n" ++
  "ins_stack:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_k:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref2:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_node:\n  .zero 131072\n" ++
  ".balign 8\n" ++
  "ins_node2:\n  .zero 131072\n" ++
  ".balign 8\n" ++
  "ins_empty_branch:\n" ++
  "  .byte 0xd1,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80\n" ++
  ".balign 8\n" ++
  "mxne_field_len:\n  .zero 8\n" ++
  "mxne_hp_len:\n  .zero 8\n" ++
  "mxne_cursor:\n  .zero 8\n" ++
  "mxne_total_payload:\n  .zero 8\n" ++
  "mxne_hp_buf:\n  .zero 1024\n" ++
  "mxne_payload_buf:\n  .zero 16384\n" ++
  -- .6.4.3.2 contract-dispatch leaf-helper scratch. Shared scratch (zk3_state,
  -- wlh_*, mnk_*, mbc_*, mw_*, mlk_*, ad_*, aa_*, hesr_*) is already provided by
  -- this guest data section, so only the slot/code-side private labels are added
  -- here (deduped against the guest object via nm). The contract-stage/self-
  -- contained/bal-find/bal-storage probe scratch uses unique prefixes (srpc_,
  -- bsc_, bfa_, brsk_) so it cannot collide.
  -- slot_at_index leaf scratch:
  ".balign 8\n" ++
  "si_value_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n  .zero 256\n" ++
  -- slot_at_header_state_root scratch:
  ".balign 32\n" ++
  "sahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "sahsr_u256:\n  .zero 32\n" ++
  -- code_at_header_state_root scratch:
  ".balign 32\n" ++
  "cahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "cahsr_acct_struct:\n  .zero 104\n" ++
  "cahsr_code_offset:\n  .zero 8\n" ++
  "cahsr_code_length:\n  .zero 8\n" ++
  -- stage_runtime_payload_code private scratch:
  ".balign 8\n" ++
  "srpc_ctx:\n  .zero 192\n" ++
  "srpc_exec:\n  .zero 512\n" ++
  "srpc_code:\n  .zero 64\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n" ++   -- 3vc2p.3b: M29 recent-blockhash table (256x32; default 0 -> inert)
  -- BLOBHASH staging: blob versioned hashes extracted from type-3 txs, written
  -- into the M28 block's blob_hash_count + blob_hashes fields by stage_runtime_payload_code.
  ".balign 8\n" ++
  "m28_blob_stage_count:\n  .zero 8\n" ++
  "m28_blob_stage_table:\n  .zero 512\n" ++  -- 16x32-byte blob hashes (runtime cap in Dispatch.lean)
  -- 3vc2p.3b sub-step B: stage_blockhash_m29 scratch (the ignored offset/length outs + the
  -- pass-1 hash sink) + blockhash_from_witness_headers' number buffer.
  ".balign 32\n" ++
  "m29_hash_tmp:\n  .zero 32\n" ++
  "m29_off_tmp:\n  .zero 8\n" ++
  "m29_len_tmp:\n  .zero 8\n" ++
  "bhfwh_number_buf:\n  .zero 8\n" ++
  "srpc_payload:\n  .zero 1024\n" ++
  -- bal_find_account_by_address private scratch:
  ".balign 8\n" ++
  "bfa_cnt:\n  .zero 8\n" ++
  "bfa_index:\n  .zero 8\n" ++
  "bfa_aoff:\n  .zero 8\n" ++
  "bfa_alen:\n  .zero 8\n" ++
  "bfa_doff:\n  .zero 8\n" ++
  "bfa_dlen:\n  .zero 8\n" ++
  "bfa_out_ptr:\n  .zero 8\n" ++
  "bfa_out_len:\n  .zero 8\n" ++
  "bfa_addr_hit:\n  .zero 20\n" ++
  "bfa_addr_miss:\n  .zero 20\n" ++
  -- coc3g.5 multi-hop: bal_same_block_delegation_code_resolve target-same-block-code
  -- fallback scratch (the single-hop target account record found in the BAL when the
  -- target's code is ALSO same-block-installed, not in the pre-state witness).
  ".balign 8\n" ++
  "bsbd_tgt_ptr:\n  .zero 8\n" ++
  "bsbd_tgt_len:\n  .zero 8\n" ++
  -- bal_recipient_storage_keys private scratch:
  ".balign 8\n" ++
  "brsk_off:\n  .zero 8\n" ++
  "brsk_len:\n  .zero 8\n" ++
  "brsk_cnt:\n  .zero 8\n" ++
  "brsk_eoff:\n  .zero 8\n" ++
  "brsk_elen:\n  .zero 8\n" ++
  "brsk_soff:\n  .zero 8\n" ++
  "brsk_slen:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "brsk_out:\n  .zero 256\n" ++
  -- .6.2.2.2.a: bal_txs_independent private scratch (the independence-guard
  -- walkers' cursors/counters; the probe's bti_bal_* fixtures are NOT needed in
  -- the verdict guest, only this scratch). All runtime-written before read.
  ".balign 8\n" ++
  "bti_acct_cnt:\n  .zero 8\n" ++
  "bti_aoff:\n  .zero 8\n" ++
  "bti_alen:\n  .zero 8\n" ++
  "bti_off:\n  .zero 8\n" ++
  "bti_len:\n  .zero 8\n" ++
  "bti_first_tx:\n  .zero 8\n" ++
  "bti_has_write:\n  .zero 8\n" ++
  "bti_conflict:\n  .zero 8\n" ++
  "bti_err:\n  .zero 8\n" ++
  "bti_rd_cnt:\n  .zero 8\n" ++
  "bti_t_cnt:\n  .zero 8\n" ++
  "bti_t_eoff:\n  .zero 8\n" ++
  "bti_t_elen:\n  .zero 8\n" ++
  "bti_t_foff:\n  .zero 8\n" ++
  "bti_t_flen:\n  .zero 8\n" ++
  "bti_sc_cnt:\n  .zero 8\n" ++
  "bti_sc_soff:\n  .zero 8\n" ++
  "bti_sc_slen:\n  .zero 8\n" ++
  "bti_sc_coff:\n  .zero 8\n" ++
  "bti_sc_clen:\n  .zero 8\n" ++
  -- .6.2.2.2.a: per-tx runtime-result arrays + context scratch for the gated
  -- multi-tx dispatch loop (.6.2.2.2.b). U64 arrays are cheap tx-indexed
  -- full-capacity arenas; the active loop gate remains bvMtxActiveTxCap until
  -- the sender-balance algorithm lands. bv_mtx_ctx is one 192-byte
  -- multi_tx_nth_context record reused per index.
  ".balign 8\n" ++
  "bv_mtx_gas_left:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_calldata:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_ctx:\n  .zero 192\n" ++
  -- bmvmx.5.5.6.3: scratch for the exact multi-tx nonce check. The
  -- running per-sender counts now live in bv_b1_sender_table after the
  -- pre-loop indexed sender aggregation.

  "bv_mtx_nonce_pre:\n  .zero 8\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2: cross-tx committed-storage table. After each per-tx dispatch
  -- the multi-tx loop upserts the live exec log's entries here, re-keyed (addrHash) to that
  -- tx's recipient (its entries are all the recipient's own because dispatch_tx_runtime_code
  -- requires self-contained), so the NEXT tx's preload can thread a prior tx's committed
  -- value via exec_log_latest_value. Capacity counts unique (recipient, slotKey) keys;
  -- duplicate writes update in place. The active chunked table keeps the same 128-entry
  -- page layout over four pages (512 unique keys total); unique-key overflow is
  -- conservative and surfaced via bv_mtx_committed_chunk_overflow. The legacy single-page
  -- labels remain while the stacked transition lands, but block-verdict call sites use the
  -- chunked count/table/overflow labels. dtrc_recipkey / dtrc_threadval are the per-slot
  -- query key and threaded-value output buffer.
  ".balign 8\n" ++
  "bv_mtx_committed_count:\n  .zero 8\n" ++
  "bv_mtx_committed_overflow:\n  .zero 8\n" ++
  "bv_mtx_committed_chunk_count:\n  .zero 8\n" ++
  "bv_mtx_committed_chunk_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_mtx_committed:\n  .zero " ++ toString bvMtxCommittedBytes ++ "\n" ++
  "bv_mtx_committed_chunked:\n  .zero " ++ toString bvMtxCommittedChunkBytes ++ "\n" ++
  "dtrc_recipkey:\n  .zero 32\n" ++
  "dtrc_threadval:\n  .zero 32\n" ++
  "dtrc_slotkey_le:\n  .zero 32\n" ++   -- ogjan: LE byte-reverse of bvcd_keys[i] for the exec_log_latest_value slotKey match
  -- coc3g.5: 20-byte EIP-7702 delegated TARGET address scratch. When the recipient's
  -- resolved code is a 0xef0100||target marker (a prior-block-delegated EOA), the
  -- dispatch follows the marker to the target's code while keeping env.ADDRESS = the
  -- delegating EOA (so SSTORE keys the EOA's storage, per interpreter.py message setup).
  ".balign 8\n" ++
  "dtrc_deleg_target:\n  .zero 32\n" ++
  -- bmvmx.1.4.4: single-tx EOA settlement scalars precomputed before
  -- block_state_root (additive; no consumer yet -> verdict byte-identical).
  -- Consumed later by .4.1/.4.2 to build execution-derived sender/coinbase leaves.
  ".balign 8\n" ++
  "bmvmx_avail:\n  .zero 8\n" ++
  "eip7708_tl_typed_avail:\n  .zero 8\n" ++
  -- Receipts completeness shape for the enforcement tail:
  --   0 unknown/none
  --   1 legacy single-tx simple EOA
  --   2 typed single-tx simple EOA
  --   3 single-tx calldata contract dispatch complete
  --   4 multi-tx EOA dispatch complete
  --   5 multi-tx contract dispatch complete
  --   60 top-level creation unsupported
  --   61 runtime dispatch miss / non-self-contained
  --   62 other multi-tx unsupported bail
  -- `bv_receipts_enforce_enabled` is the stable gate bit consumed by
  -- BlockVerdictReceiptsTail; the older availability flags remain as
  -- compatibility/debug signals for the paths that originally introduced them.
  "bv_receipts_completeness_shape:\n  .zero 8\n" ++
  "bv_receipts_enforce_enabled:\n  .zero 8\n" ++
  "bmvmx_gas_used:\n  .zero 8\n" ++
  "bmvmx_txoff:\n  .zero 8\n" ++
  "bmvmx_ctx:\n  .zero 192\n" ++
  ".balign 32\n" ++
  "bmvmx_value:\n  .zero 32\n" ++
  "bmvmx_eff_gas_price:\n  .zero 32\n" ++
  "bmvmx_priority_fee:\n  .zero 32\n" ++
  "bmvmx_basefee_be:\n  .zero 32\n" ++
  -- bmvmx.1.4.1: execution-derived sender balance debit (gas_used*eff_gas_price + value),
  -- the sender's balance decrease for the supported single-tx EOA class.
  "bmvmx_gascost:\n  .zero 32\n" ++
  "bmvmx_sender_debit:\n  .zero 32\n" ++
  -- bmvmx.1.4.2: execution-derived coinbase fee credit (priority_fee_per_gas * gas_used).
  "bmvmx_coinbase_credit:\n  .zero 32\n" ++
  -- .6.2.2.2.b: multi-tx dispatch loop index cursor.
  "bv_mtx_i:\n  .zero 8\n" ++
  -- fhsxz.2.4.2.57.11.6.5: parent (PRE-state) header RLP ptr/len, stashed by
  -- block_verdict from its input frame (8(s0)/16(s0)). dispatch_tx_runtime_code's
  -- witness lookups (code/slot/balance_at_header_state_root) MUST use the PRE-state
  -- root (the witness is the parent's post-state = this block's pre-state proof),
  -- not sv_this_rlp (this block's POST-state header), else a recipient whose account
  -- changes within the block (e.g. an SSTORE contract) is unprovable -> false bail.
  ".balign 8\n" ++
  "sv_pre_rlp_ptr:\n  .zero 8\n" ++
  "sv_pre_rlp_len:\n  .zero 8\n" ++
  "bv_witness_state_ptr:\n  .zero 8\n" ++
  "bv_witness_state_len:\n  .zero 8\n" ++
  -- fhsxz.2.4.2.57.11.6.5: mtx-gating for dispatch_tx_runtime_code's witness lookups.
  -- dtrc_use_pre_header: 0 (default) -> use sv_this_rlp (POST header; single-tx path,
  -- conservative, identical to #8686); 1 -> use sv_pre_rlp_* (PRE/parent header; set by
  -- the mtx loop ONLY around its dispatch call so multi-tx contract dispatch can prove
  -- recipient state against the witness root. dtrc_hdr_ptr/len: the header ptr+len
  -- resolved ONCE at dispatch entry from the flag, read by all 5 lookup sites.
  ".balign 8\n" ++
  "dtrc_use_pre_header:\n  .zero 8\n" ++
  "dtrc_hdr_ptr:\n  .zero 8\n" ++
  "dtrc_hdr_len:\n  .zero 8\n" ++
  -- coc3g.5 multi-hop: scratch for locating the type-4 authorization_list span.
  "dtrc_auth_off:\n  .zero 8\n" ++
  "dtrc_auth_len:\n  .zero 8\n" ++
  -- bmvmx.1.4.2 compare: validate the coinbase credit against the BAL (additive; match flag only).
  ".balign 8\n" ++
  "bmvmx_coinbase_addr:\n  .zero 20\n" ++
  ".balign 8\n" ++
  "bmvmx_acct:\n  .zero 104\n" ++
  "bmvmx_cb_acct_ptr:\n  .zero 8\n" ++
  "bmvmx_cb_acct_len:\n  .zero 8\n" ++
  "bmvmx_cb_bal_len:\n  .zero 8\n" ++
  "bmvmx_cb_nonce_len:\n  .zero 8\n" ++
  "bmvmx_coinbase_match:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bmvmx_cb_balbytes:\n  .zero 32\n" ++
  "bmvmx_cb_post:\n  .zero 32\n" ++
  "bmvmx_cb_expected:\n  .zero 32\n" ++
  "bmvmx_cb_nonce:\n  .zero 32\n" ++
  -- bmvmx.1.4.1 compare: sender address + match flag (reuses bmvmx_acct/bmvmx_cb_* scratch,
  -- which the sender compare runs through before the coinbase compare).
  ".balign 8\n" ++
  "bmvmx_sender_addr:\n  .zero 20\n" ++
  -- 3vc2p.1: scratch for the derived tx.sender staged into env CALLER/ORIGIN by
  -- stage_runtime_payload_code (contract-recipient path).
  ".balign 8\n" ++
  "srpc_sender_addr:\n  .zero 20\n" ++
  -- 3vc2p.2: effective_gas_price + priority-fee scratch for the env.gasPrice staging.
  ".balign 8\n" ++
  "gp_egp:\n  .zero 32\n" ++
  "gp_prio:\n  .zero 32\n" ++
  -- i3djw.3: skip-list for the all-accounts non-storage comparator (32B-strided
  -- {recipient, sender, coinbase} plus system addresses, pinned outside the exec log).
  ".balign 8\n" ++
  "i3djw_skip_list:\n  .zero 288\n" ++   -- coc3g.6.5: 3 {recipient,sender,coinbase} + 6 system addresses (9*32)
  -- bmvmx.5.5.1 (umbrella-A1): MULTI-TX skip-list for the all-accounts exec-vs-BAL
  -- comparators. A multi-tx block's gas/value-coupled accounts are {sender_i,
  -- recipient_i} for every tx i plus the shared {coinbase} and 6 system addresses -> up to 2N+7 entries
  -- (N = bv_tx_count <= bvMtxFullTxCap). The skip list has 2N+7
  -- entries, 32-byte-strided,
  -- address in the first 20 bytes (zero-padded). bv_mtx_skip_idx is the build-loop
  -- cursor (kept in memory so it survives the address_from_pubkey/multi_tx_nth_context
  -- calls); bv_mtx_skip_ctx is the scratch record for re-extracting each recipient.
  ".balign 8\n" ++
  "bv_mtx_skip_list:\n  .zero " ++ toString bvMtxSkipListBytes ++ "\n" ++
  "bv_mtx_skip_count:\n  .zero 8\n" ++
  "bv_mtx_skip_idx:\n  .zero 8\n" ++
  "bv_mtx_skip_ctx:\n  .zero 192\n" ++
  -- bmvmx.5.5.1 (umbrella-A2a): per-account aggregation of exec_nonstorage_effect_log
  -- for the multi-tx nonstorage comparators. record_nonstorage_effect APPENDS one record
  -- per CALL, so a multi-tx-touched account has N records; fold them into one entry keyed
  -- by the 20B BE address (first-seen pre kept, last-seen post overwritten) so the per-
  -- account comparator sees the block-aggregate {pre, post}. Dedup -> count <= the log cap,
  -- so cap x 112 B suffices. Interpolated as nonstorageEffectLogCap * 112 (NonstorageEffectLog.lean):
  -- the .Lbv_agg_append / nonstorage_effect_aggregate path has no separate bounds check, so an
  -- undersized buffer is a heap overflow; tying it to the cap keeps it correct as the cap is lifted.
  ".balign 8\n" ++
  "exec_nonstorage_effect_agg_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_agg:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  -- fva3w: pre-tx snapshots of the exec effect logs. A top-level tx that REVERTS or
  -- exceptionally aborts discards ALL its state changes (the spec rolls them back), so the
  -- value-transfer / CREATE non-storage + code effects recorded during it must be discarded
  -- too. Child frames already roll back via frame_return; but a top-level abort (INVALID /
  -- REVERT / OOG at depth 0) takes .exit_*_top with NO frame_return -> the effects survived,
  -- and the all-accounts non-storage comparator then saw a value change the BAL (correctly,
  -- net-zero) omitted -> bv_fail=44 (bal_aborted_account_access invalid/revert-call/callcode).
  -- Snapshot before the tx runtime dispatch; truncate back to it when the tx errored (status 0).
  ".balign 8\n" ++
  "bv_tx_effect_snap_ns_count:\n  .zero 8\n" ++
  "bv_tx_effect_snap_ns_overflow:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_count:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_next:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_overflow:\n  .zero 8\n" ++
  "bv_tx_effect_snap_storage_count:\n  .zero 8\n" ++   -- bbow4.2: storage exec-log count (evm_env+448) snapshot for tx-error truncation
  -- bmvmx.5.5.2 (umbrella-B1): scratch for the multi-tx per-sender FINAL-nonce check
  -- (BAL sender post nonce == pre + total sender tx count). bv_b1_finals is the 88-byte
  -- bal_account_nonstorage_finals output (separate from c2nsc_finals, which A2a's
  -- comparator uses); bv_b1_acct_ptr/len receive the sender's BAL AccountChanges.
  -- bv_b1_sender_table is sized to bvMtxSenderCountEntries distinct senders, which
  -- follows the full 200M tx-count target. Each row is a 32-byte padded address
  -- plus u64 total tx count, filled by b1_sender_count_table.
  ".balign 8\n" ++
  b1SenderCountTableScratchDataSection ++
  ".balign 8\n" ++
  "bv_b1_sender_count:\n  .zero 8\n" ++
  "bv_b1_sender_table:\n  .zero " ++ toString bvMtxSenderCountTableBytes ++ "\n" ++
  "bv_b1_count:\n  .zero 8\n" ++
  "bv_b1_expected:\n  .zero 8\n" ++
  "bv_b1_acct_ptr:\n  .zero 8\n" ++
  "bv_b1_acct_len:\n  .zero 8\n" ++
  "bv_b1_finals:\n  .zero 88\n" ++
  -- bmvmx.5.5.2.2.2 (B2.2): per-sender running balance table for multi-tx sender debits.
  -- Entries are 64B: sender address lane (first 20B used) + running u256 BE balance.
  -- Capacity follows bvMtxActiveTxCap so all-distinct current-fixture blocks do
  -- not hit the old 16-entry table-full path. Full 9523-tx aggregation is a
  -- separate follow-up slice.
  "bv_b2_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_b2_table:\n  .zero " ++ toString bvMtxSenderBalanceTableBytes ++ "\n" ++
  "bv_b2_debit_out:\n  .zero 48\n" ++
  -- B2.3 typed-tx fee scratch (bmvmx.5.5.2.2.6): the B2.2 loop adds the type-4 AUTH_BASE
  -- and type-3 blob-data-gas sender-debit terms that multi_tx_actual_sender_debit omits,
  -- so type-3/4 senders are debited exactly and B2.3 enforces them. txtype/innoff from
  -- tx_type_dispatch; authoff/authlen/authcount = auth-list RLP; blobcount = blob hashes;
  -- feedebit = the u256 fee accumulator added into the sender debit.
  "bv_b23_txtype:\n  .zero 8\n" ++
  "bv_b23_innoff:\n  .zero 8\n" ++
  "bv_b23_authoff:\n  .zero 8\n" ++
  "bv_b23_authlen:\n  .zero 8\n" ++
  "bv_b23_authcount:\n  .zero 8\n" ++
  "bv_b23_blobcount:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_b23_feedebit:\n  .zero 32\n" ++
  "mtxsd_gascost:\n  .zero 32\n" ++
  -- i3djw.3: scratch for bal_all_accounts_nonstorage_consistent + its per-account deps
  -- (bal_account_nonstorage_consistent / _finals). rfu_* is already linked (other rlp users).
  ".balign 8\n" ++
  "c3ns_acct_count:\n  .zero 8\n" ++
  "c3ns_acct_off:\n  .zero 8\n" ++
  "c3ns_acct_len:\n  .zero 8\n" ++
  "c3ns_addr_off:\n  .zero 8\n" ++
  "c3ns_addr_len:\n  .zero 8\n" ++
  "c3ns_lenient_notfound:\n  .zero 8\n" ++   -- bmvmx.5.5.1 (A2a): 0 strict (single-tx), 1 lenient (multi-tx)
  "c2nsc_finals:\n  .zero 88\n" ++
  "c2nsf_off:\n  .zero 8\n" ++
  "c2nsf_len:\n  .zero 8\n" ++
  "c2nsf_cnt:\n  .zero 8\n" ++
  "c2nsf_toff:\n  .zero 8\n" ++
  "c2nsf_tlen:\n  .zero 8\n" ++
  "c2nsf_coff:\n  .zero 8\n" ++
  "c2nsf_clen:\n  .zero 8\n" ++
  -- i3djw.3 reverse: scratch for bal_all_accounts_nonstorage_covers.
  "c3cov_acct_count:\n  .zero 8\n" ++
  "c3cov_acct_off:\n  .zero 8\n" ++
  "c3cov_acct_len:\n  .zero 8\n" ++
  "c3cov_addr_off:\n  .zero 8\n" ++
  "c3cov_addr_len:\n  .zero 8\n" ++
  -- bmvmx.5.5.7.3 step c: matched-bitmap for the LINEARIZED bal_all_accounts_nonstorage_covers
  -- (1 byte per agg entry, indexed by agg index). MUST be >= nonstorageEffectLogCap bytes.
  "c3cov_covered:\n  .zero " ++ toString nonstorageEffectLogCap ++ "\n" ++
  -- i3djw.4: scratch for bal_all_accounts_code_consistent (FORWARD per-account CODE compare,
  -- with the EIP-7702 delegation skip). bacc_finals is the per-account 88-byte finals scratch
  -- consumed by bal_account_code_consistent; baac_* are the account-iteration scratch. The
  -- c2nsf_*/rfu_* scratch the inlined finals helper needs is already provided just above.
  ".balign 8\n" ++
  "baac_acct_count:\n  .zero 8\n" ++
  "baac_acct_off:\n  .zero 8\n" ++
  "baac_acct_len:\n  .zero 8\n" ++
  "baac_addr_off:\n  .zero 8\n" ++
  "baac_addr_len:\n  .zero 8\n" ++
  "bacc_finals:\n  .zero 88\n" ++
  -- yisv8.1: recipient self-balance scratch for the env.SELFBALANCE (word 1) staging.
  ".balign 32\n" ++
  "yisv8_self_bal:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bmvmx_sender_match:\n  .zero 8\n" ++
  -- bmvmx.1.4.3.1: envelope predicate scratch. bmvmx_sender_checked / bmvmx_coinbase_checked
  -- mark that the exec-derived balance compare was PERFORMED in the cheap envelope (single-tx
  -- + legacy) with the relevant addresses distinct (sender!=recipient/coinbase for the sender
  -- compare; coinbase!=sender/recipient for the coinbase compare). .4.3.2 completes the
  -- envelope with the deferred EOA-recipient check and then gates the verdict reject on
  -- (avail && checked && EOA && !match), without false-rejecting skipped / out-of-envelope /
  -- overlapping blocks.
  ".balign 8\n" ++
  "bmvmx_sender_checked:\n  .zero 8\n" ++
  "bmvmx_coinbase_checked:\n  .zero 8\n" ++
  -- bmvmx.1.6.3 (balance slice): scratch for the execution-derived sender balance compare
  -- (tx_gas_bal_post_verify_runtime + sender_debit_from_gas). tea_*/u256m_acc/tgsbl_*/bpf_*/
  -- tefgp_* are already provided by the EOA tx_gas_bal_post_verify path; only sdfg_gascost
  -- (sender_debit) and the tgbpvr_* / output buffer are new.
  ".balign 32\n" ++
  "sdfg_gascost:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_in:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "tgbpvr_pre:\n  .zero 32\n" ++
  "tgbpvr_post:\n  .zero 32\n" ++
  "tgbpvr_egp:\n  .zero 32\n" ++
  "tgbpvr_prio:\n  .zero 32\n" ++
  "tgbpvr_value:\n  .zero 32\n" ++
  "tgbpvr_gasdebit:\n  .zero 32\n" ++
  "tgbpvr_expected:\n  .zero 32\n" ++
  "tgbpvr_zero:\n  .zero 32\n" ++
  "tgbpvr_blobdebit:\n  .zero 32\n" ++
  "tgbpvr_authdebit:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_to:\n  .zero 24\n" ++
  "tgbpvr_iscreation:\n  .zero 8\n" ++
  "tgbpvr_tx_type:\n  .zero 8\n" ++
  "tgbpvr_inner_off:\n  .zero 8\n" ++
  "tgbpvr_blob_count:\n  .zero 8\n" ++
  "tgbpvr_auth_off:\n  .zero 8\n" ++
  "tgbpvr_auth_len:\n  .zero 8\n" ++
  "tgbpvr_auth_count:\n  .zero 8\n" ++
  "tgbpvr_lookup:\n  .zero 168\n" ++
  ".balign 8\n" ++
  "bv_sender_bal_check:\n  .zero 192\n" ++
  -- bmvmx.2: scratch for the check_transaction upfront-balance pre-validation
  -- (sender_pre_balance >= gas_limit*max_fee_per_gas + blob_gas*max_fee_per_blob_gas
  -- + tx.value). bv_upfront_cost holds the cumulative upfront cost; bv_upfront_islt
  -- is the u256_lt_be verdict (1 iff pre_balance < upfront -> reject).
  ".balign 8\n" ++
  "bv_upfront_cost:\n  .zero 32\n" ++
  "bv_upfront_blob_cost:\n  .zero 32\n" ++
  "bv_upfront_blob_count:\n  .zero 8\n" ++
  "bv_upfront_islt:\n  .zero 8\n" ++
  -- bmvmx.5: out scratch for the hoisted single-tx fee-validity gate's
  -- tx_effective_gas_pricing call (effective_gas_price / priority_fee_per_gas, 32B BE
  -- each). Only the call's status (2/3) is consumed; the values are unused here.
  ".balign 8\n" ++
  "bv_fee_egp_scratch:\n  .zero 32\n" ++
  "bv_fee_prio_scratch:\n  .zero 32\n" ++
  -- bmvmx.5: block base_fee (BE, 32B) for the multi-tx fee gate -- multi_tx_nth_context does
  -- not fill the record's base_fee, so the mtx loop reverses the payload LE base_fee here once.
  "bv_mtx_base_fee_be:\n  .zero 32\n" ++
  -- Live coinbase fee effect scratch for multi-tx BALANCE(COINBASE) reads.
  ".balign 8\n" ++
  "bv_mtx_cbfee_receipt_inc:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_mtx_cbfee_egp:\n  .zero 32\n" ++
  "bv_mtx_cbfee_priority:\n  .zero 32\n" ++
  "bv_mtx_cbfee_credit:\n  .zero 32\n" ++
  "bv_mtx_cbfee_pre:\n  .zero 32\n" ++
  "bv_mtx_cbfee_post:\n  .zero 32\n" ++
  -- bmvmx.5: per-mtx-tx sender scratch for the multi-tx nonce lower-bound check. sender address
  -- (address_from_pubkey of the verified public_keys[i]) + the sender's pre-state account
  -- (account_at_header_state_root output; nonce@0).
  "bv_mtx_sender_addr:\n  .zero 32\n" ++
  "bv_mtx_sender_acct:\n  .zero 128\n" ++
  -- bmvmx.5: single-tx contract-recipient sender scratch (same role as the mtx pair, i=0 path).
  "bv_stx_sender_addr:\n  .zero 32\n" ++
  "bv_stx_sender_acct:\n  .zero 128\n" ++
  -- bmvmx.1.6.6: scratch for the all-accounts per-slot tuple-sequence check (#8606). batsc_* is
  -- the wrapper's own scratch; the sub-helpers' scratch (atsc_*/bts_*/els_*) come from their Data
  -- defs. rfu_* (rlp_field_to_u64) is already provided above; slot_tuple_sequences_match is
  -- self-contained.
  ".balign 8\n" ++
  "batsc_acct_count:\n  .zero 8\n" ++
  "batsc_acct_off:\n  .zero 8\n" ++
  "batsc_acct_len:\n  .zero 8\n" ++
  "batsc_addr_off:\n  .zero 8\n" ++
  "batsc_addr_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "batsc_key:\n  .zero 32\n" ++ "\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++
  balSlotTupleSequenceData ++ "\n" ++
  execLogSlotTuplesData

end EvmAsm.Codegen
