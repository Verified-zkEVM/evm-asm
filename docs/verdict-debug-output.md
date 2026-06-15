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
| 464 | 8 | `runtime_completeness_status` |
| 472 | 16 | `mtx_committed_overflow`, `mtx_committed_count` |
| 488 | 136 | `widx_build_status`, `widx_build_section_len`, `widx_build_count`, `widx_enabled`, `wlh_lookup_calls`, `wlh_indexed_calls`, `wlh_indexed_hits`, `wlh_indexed_misses`, `wlh_linear_calls`, `wlh_linear_hits`, `wlh_linear_misses`, `wlh_linear_iterations`, `wlh_linear_last_section_len`, `wlh_linear_max_section_len`, `svf_codes_len`, `svf_headers_len`, `svf_headers_count` |

The current final byte is `OUTPUT + 624`. The smoke check emits/links both the
normal probe and the experimental BSR-cap patched probe, then verifies the shell
formatter reaches the final emitted word.
