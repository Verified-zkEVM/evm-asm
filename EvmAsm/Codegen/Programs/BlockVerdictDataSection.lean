/-
  EvmAsm.Codegen.Programs.BlockVerdictDataSection

  Data-section (BSS/static arenas) for the stateless verdict v2 program.
  Carved out of BlockVerdict.lean to stay within the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.StatelessVerdict
import EvmAsm.Codegen.Programs.RequestsHash
import EvmAsm.Codegen.Programs.BalAccountHasStateChange
import EvmAsm.Codegen.Programs.BalModeledSystem
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransfer
import EvmAsm.Codegen.Programs.Eip7702NonceReuseGuard

namespace EvmAsm.Codegen

def ziskStatelessVerdictV2DataSection : String :=
  ziskStatelessVerdictDataSection ++ "\n" ++
  runtimeAccessAccountOutcomeData ++ "\n" ++
  storageAccessGasData ++ "\n" ++
  executionRequestsHashDataSection ++ "\n" ++
  ".balign 32\n" ++
  "svf_bal_hash:\n  .zero 32\n" ++
  "svf_transactions_root:\n  .zero 32\n" ++
  "svf_withdrawals_root:\n  .zero 32\n" ++
  "bv_block_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bv_block_hash_check_enabled:\n  .zero 8\n" ++
  ".balign 8\n" ++
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
  "bv_block_rlp_len:\n  .zero 8\n" ++
  "bv_blockhash_required_headers:\n  .zero 8\n" ++
  "bv_versioned_hashes_len:\n  .zero 8\n" ++
  "bv_blob_gas_expected:\n  .zero 8\n" ++
  "bv_blob_gas_observed:\n  .zero 8\n" ++
  "brr_status:\n  .zero 8\n" ++
  "brr_append_status:\n  .zero 8\n" ++
  "brr_tx_type:\n  .zero 8\n" ++
  "brr_tx_inner:\n  .zero 8\n" ++
  "brr_tx_gas:\n  .zero 8\n" ++
  "brr_receipt_gas_ptr:\n  .zero 8\n" ++
  "brr_receipt_gas_count:\n  .zero 8\n" ++
  "brr_control:\n  .zero 24\n" ++
  ".balign 8\n" ++
  "brr_records:\n  .zero 1024\n" ++
  "bvgr_runtime_gas_left_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_refund_counter_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_calldata_floor_ptr:\n  .zero 8\n" ++
  "bvgr_runtime_count:\n  .zero 8\n" ++
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
  "bvgr_tx_gas_limits:\n  .zero 128\n" ++
  "bvgr_gas_left:\n  .zero 128\n" ++
  "bvgr_refund_counter:\n  .zero 128\n" ++
  "bvgr_calldata_floor:\n  .zero 128\n" ++
  "bvgr_block_gas_increments:\n  .zero 128\n" ++
  "bvgr_receipt_gas_increments:\n  .zero 128\n" ++
  "bvgr_before_refund:\n  .zero 128\n" ++
  "bvgr_applied_refund:\n  .zero 128\n" ++
  blockVerdictTxGasPrechargeDataSection ++
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
  "svf_headers_ptr:\n  .zero 8\n" ++
  "svf_headers_len:\n  .zero 8\n" ++
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
  ".balign 32\n" ++
  "bv_tx_recipient_code_hash:\n  .zero 32\n" ++
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
  ".balign 32\n" ++
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
  "bsg_header_gas_used:\n  .zero 8\n" ++
  "bsg_min_block_gas:\n  .zero 8\n" ++
  "alc_scratch:\n  .zero 8\n" ++
  "alc_entry_offset:\n  .zero 8\n" ++
  "alc_entry_length:\n  .zero 8\n" ++
  "alc_keys_offset:\n  .zero 8\n" ++
  "alc_keys_length:\n  .zero 8\n" ++
  "bsg_worst_state:\n  .zero 8\n" ++
  "bsg_prior_state:\n  .zero 8\n" ++
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
  "baap_storage_desc:\n  .zero " ++ toString (bsrMaxBalItems * baapStorageDescBytes) ++ "\n" ++
  "baap_storage_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
  "baap_storage_delete_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
  "baap_storage_values:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++ "\n" ++
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
  "\nbasr_values:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  "\nbasr_accounts:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++ "\n" ++
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
  "ins_node:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_node2:\n  .zero 2048\n" ++
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
  "mxne_payload_buf:\n  .zero 16384\n"

end EvmAsm.Codegen
