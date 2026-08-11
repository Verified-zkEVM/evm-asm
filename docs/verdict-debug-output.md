# Stateless Verdict Debug Output

`zisk_stateless_verdict_v2` writes an append-only debug stream at
`OUTPUT + 0`. The first word is the verdict bit; later words are diagnostic
only and must not affect verdict semantics. `scripts/codegen-eest-stateless-check.sh`
decodes this stream in `format_verdict_debug`.

When adding fields, append new u64 words after the last offset, update the
formatter in the same PR, and run
`scripts/codegen-zisk-stateless-verdict-debug-smoke.sh`. Existing offsets are
ABI-stable for EEST triage logs.

| Offset | Size | Label(s) |
| ---: | ---: | --- |
| 0 | 168 | `verdict`, `bv_fail`, `header`, `state`, `bal_count`, `bsr_fail`, `change_count`, `witness_len`, `baacd_fail`, `bacv_fail`, `baap_fail`, `block_inc0`, `block_inc1`, `tx_state0`, `tx_state1`, `exact_net_status`, `exact_net_index`, `exact_block_status`, `exact_header_gas_used`, `exact_expected_gas_used`, `receipt1_cumulative` |
| 168 | 32 | `recomputed_state_root` |
| 200 | 32 | `payload_state_root` |
| 232 | 24 | `gas_arena_status`, `gas_arena_tx_count`, `gas_arena_runtime_count` |
| 344 | 32 | `st_status`, `st_sender_status`, `st_recipient_status`, `st_fee_status` |
| 376 | 16 | `wd_root_status`, `wd_root_valid` |
| 392 | 16 | `tx_root_status`, `tx_count` |
| 408 | 16 | `receipts_shape`, `receipts_enforce` |
| 424 | 8 | `receipts_validator_status` |
| 432 | 8 | `receipts_encoder_status` |
| 440 | 16 | `receipt_logs_status`, `block_log_overflow` |
| 456 | 8 | `dispatch_runtime_status` |
| 464 | 8 | _(retired #12064)_ — was `runtime_completeness_status` (debug-only, never gated); dump removed; offset unused |
| 472 | 16 | `mtx_committed_overflow`, `mtx_committed_count` |
| 488 | 48 | `system_capture_status`, `system_capture_start`, `system_capture_end`, `system_capture_rows`, `system_capture_old_count`, `system_capture_new_count` |
| 536 | 136 | `widx_build_status`, `widx_build_section_len`, `widx_build_count`, `widx_enabled`, `wlh_lookup_calls`, `wlh_indexed_calls`, `wlh_indexed_hits`, `wlh_indexed_misses`, `wlh_linear_calls`, `wlh_linear_hits`, `wlh_linear_misses`, `wlh_linear_iterations`, `wlh_linear_last_section_len`, `wlh_linear_max_section_len`, `svf_codes_len`, `svf_headers_len`, `svf_headers_count` |
| 672 | 96 | `request_dstatus`, `request_dlen`, `request_dbody_cap`, `request_log_records_cap`, `request_wlen`, `request_clen`, `request_system_body_cap`, `request_er_assembled_len`, `request_er_assembled_cap`, `request_erh_status`, `request_erh_blob_cap`, `request_notx_deposit_len` (retired/zero) |
| 768 | 128 | `mtx_arena_tx_cap`, `mtx_full_200m_tx_cap`, `mtx_u64_arena_bytes`, `mtx_log_window_bytes`, `mtx_skip_list_cap`, `mtx_skip_count`, `mtx_loop_index`, `mtx_sender_count_cap`, `mtx_sender_count`, `mtx_sender_balance_cap`, `mtx_sender_balance_count`, `mtx_committed_chunk_cap`, `mtx_committed_chunk_bytes`, `mtx_nonce_seen_count`, `mtx_nonce_seen_cap`, `mtx_tx_count` |
| 896 | 136 | `receipt_record_count`, `receipt_record_cap`, `receipt_records_status`, `receipt_append_status`, `block_log_count`, `block_log_desc_cap`, `block_log_data_used`, `block_log_data_cap`, `logs_rlp_arena_used`, `logs_rlp_arena_cap`, `logs_rlp_last_len`, `receipts_rlp_len`, `receipts_rlp_cap`, `record_bloom_bytes_used`, `record_bloom_bytes_cap`, `receipt_logs_status_mirror`, `block_log_overflow_mirror` |
| 1032 | 96 | `wcidx_build_status`, `wcidx_build_section_len`, `wcidx_build_count`, `wcidx_enabled`, `wclh_lookup_calls`, `wclh_indexed_calls`, `wclh_indexed_hits`, `wclh_indexed_misses`, `wclh_linear_calls`, `wclh_linear_hits`, `wclh_linear_misses`, `wclh_linear_iterations` |

The current final byte is `OUTPUT + 1128`. The smoke check emits/links both the
normal probe and the experimental BSR-cap patched probe, then verifies the shell
formatter reaches the final emitted word.
