# Guest-image CodeReq coverage accounting (bead evm-asm-4ch8f.63)

What fraction of the linked `stateless_guest` `.text` the composed
`guestImageCodeReq` (`EvmAsm/Codegen/Proofs/GuestImage.lean`, entries table
`GuestImageEntries.lean`) actually covers, and the precise list of what it
does NOT — every uncovered range is work someone must do before the `.64`
end-to-end theorem can run over the FULL image. Child beads under `.63`
track the clusters (§2).

**Regenerate** (after any layout/manifest change):

```
python3 scripts/guest_image_coverage.py            # summary + gaps
python3 scripts/guest_image_coverage.py --md       # this file's §3 table
python3 scripts/guest_image_coverage.py --emit-lean  # GuestImageEntries.lean
```

Method: `.text` symbol extents come from the linker-facts table
(`scripts/asm-fixtures/symbol-addresses.tsv`, CI-drift-guarded); a symbol's
extent runs to the next symbol (or the `RegionMap.textSizeBytes` end). A
range is covered iff its symbol is a wave-.9 conversion
(`scripts/asm-fixtures/MANIFEST.tsv`) whose `_prog` length (the
kernel-checked `#guard <prog>.length` pin) fills the extent; a shorter
`_prog` leaves a `TAIL` gap, a longer one is an `OVERRUN` (hard error =
layout drift). The script asserts covered + gaps = `textSizeBytes` exactly.

Manifest entries whose entry symbol is NOT in the TSV are **converted but
not linked** (26 of 384 today — gas helpers etc. awaiting wiring); they are
excluded from `guestImageEntries` (the image `CodeReq` must reflect the
emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80059418), 365592 bytes (`RegionMap.textSizeBytes = 0x59418`)

- symbols in `.text`: 801 (358 converted, 443 unconverted)
- covered by converted `_prog`s: 86872 bytes (23.76%)
- NOT covered: 278720 bytes (76.24%), 443 ranges

Everything covered is anchored BY NAME (`GuestAddrs.<entry>`), so layout
regens flow through `GuestAddrs.lean` without touching the entries table
(addresses) — only add/remove of functions or length changes regenerate it.
The kernel-checked extent fact `guestImageEntries_extentsOk`
(`GuestImage.lean`) is the whole-image disjointness certificate.

## 2. Gap clusters → child beads

| cluster | bytes | ranges | notes |
|---|---|---|---|
| EVM opcode handlers (`h_*`) + dispatch runtime (`dispatch_*`, `runtime_*`, `frame_*`, `call_frame_*`) | ~101 KB | ~120 | the interpreter loop — bead `.10`/`.49`–`.59` territory; `h_CALL` family alone is ~53 KB |
| block verdict + orchestration (`block_verdict` 36 KB, `block_*`, `stateless_verdict_v2`, `eip8037_*`) | ~55 KB | ~25 | bead `.36`/`.37`/`.41`–`.47`/`.61`/`.62` territory |
| BAL validators (`bal_*`, `bbcv_*`, `capture_*`, `append_*`) | ~22 KB | 40 | |
| crypto kernels: modexp (`modexp*`, `mx_*`, `modexp_bn_*` buffers-in-text) | ~15 KB | 13 | bead `.11` strategy scope |
| crypto accel bridges (`zkvm_*`) | ~17 KB | 15 | includes `zkvm_bls12_map_fp*` ~11 KB |
| bls12-381 / bn254 / secp256k1 / ripemd160 stragglers | ~10 KB | 23 | |
| tx family (`tx_*`, eip7702 authority/refund) | ~11 KB | 14 | |
| `_start` + guest shell (`sg_*` helpers; validator pipeline/NPR/stamp live inside the `_start`..`zkvm_sha256` extent) | ~6 KB | 9 | the `.63` pipeline-triple half |
| witness db + mpt + rlp leaves | ~6 KB | 23 | |
| system calls + requests + receipts (`scc_*`, `stage_*`, `derive_*`, `parse_deposit*`, `assemble_*`, `requests_*`, `receipt*`, `materialize_*`, `log_*`) | ~7 KB | 20 | 8uld3.2.3 additions |
| remaining small leaves (ssz-htr shell, `account_*`, `chain_config_valid`, `public_keys_valid`, u256/u128 helpers, misc) | ~28 KB | ~140 | long tail of unconverted leaf routines |

(Cluster sums are approximate binnings of the exact table in §3; the §3
table and the script are authoritative.)

## 3. Full gap table (generated)

| start | end | bytes | symbol | kind |
|---|---|---|---|---|
| `0x80000000` | `0x800012b8` | 4792 | `_start` | UNCONVERTED |
| `0x80001ab8` | `0x80001ae8` | 48 | `sg_load_u32le` | UNCONVERTED |
| `0x80001ae8` | `0x80001b08` | 32 | `sg_memcpy` | UNCONVERTED |
| `0x80001b08` | `0x80001d38` | 560 | `ssz_htr_withdrawals` | UNCONVERTED |
| `0x80001d38` | `0x80001d9c` | 100 | `sg_htr_bv48` | UNCONVERTED |
| `0x80001d9c` | `0x80001df4` | 88 | `sg_htr_bv96` | UNCONVERTED |
| `0x80001df4` | `0x80001ed4` | 224 | `sg_htr_deposit` | UNCONVERTED |
| `0x80001ed4` | `0x80001f88` | 180 | `sg_htr_wr` | UNCONVERTED |
| `0x80001f88` | `0x80002020` | 152 | `sg_htr_cr` | UNCONVERTED |
| `0x80002020` | `0x80002120` | 256 | `sg_htr_clist` | UNCONVERTED |
| `0x80002120` | `0x80002220` | 256 | `ssz_htr_execution_requests` | UNCONVERTED |
| `0x80003264` | `0x800034d0` | 620 | `witness_lookup_by_hash` | UNCONVERTED |
| `0x800034d0` | `0x800034ec` | 28 | `widx_record_ptr` | UNCONVERTED |
| `0x800034ec` | `0x8000352c` | 64 | `widx_cmp32` | UNCONVERTED |
| `0x8000352c` | `0x8000355c` | 48 | `widx_swap_records` | UNCONVERTED |
| `0x8000355c` | `0x80003658` | 252 | `widx_sift_down` | UNCONVERTED |
| `0x80003658` | `0x800038d0` | 632 | `witness_index_build` | UNCONVERTED |
| `0x800038d0` | `0x80003998` | 200 | `witness_lookup_by_hash_indexed` | UNCONVERTED |
| `0x80003998` | `0x80003c04` | 620 | `witness_codes_lookup_by_hash` | UNCONVERTED |
| `0x80003c04` | `0x80003c20` | 28 | `wcidx_record_ptr` | UNCONVERTED |
| `0x80003c20` | `0x80003c60` | 64 | `wcidx_cmp32` | UNCONVERTED |
| `0x80003c60` | `0x80003c90` | 48 | `wcidx_swap_records` | UNCONVERTED |
| `0x80003c90` | `0x80003d8c` | 252 | `wcidx_sift_down` | UNCONVERTED |
| `0x80003d8c` | `0x80004004` | 632 | `witness_codes_index_build` | UNCONVERTED |
| `0x80004004` | `0x800040cc` | 200 | `witness_codes_lookup_by_hash_indexed` | UNCONVERTED |
| `0x8000472c` | `0x800047b8` | 140 | `rlp_item_size` | UNCONVERTED |
| `0x800047b8` | `0x8000488c` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x8000488c` | `0x80004960` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004960` | `0x80004afc` | 412 | `rlp_walk_next` | UNCONVERTED |
| `0x80004afc` | `0x80004b54` | 88 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80004b54` | `0x80004bbc` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x80004bbc` | `0x80004db0` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80008fd8` | `0x8000919c` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x8000919c` | `0x80009208` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a6d0` | `0x8000ac60` | 1424 | `block_header_ssz_to_rlp` | UNCONVERTED |
| `0x8000afcc` | `0x8000b158` | 396 | `execution_requests_hash` | UNCONVERTED |
| `0x8000b158` | `0x8000b1b4` | 92 | `erh_hash_one` | UNCONVERTED |
| `0x8000cb74` | `0x8000dad4` | 3936 | `bal_account_apply_post_fields` | UNCONVERTED |
| `0x8000eda0` | `0x8000ef9c` | 508 | `capture_system_storage_exec_rows` | UNCONVERTED |
| `0x8000ef9c` | `0x8000f188` | 492 | `append_modeled_system_storage_tuple_rows` | UNCONVERTED |
| `0x8000f188` | `0x8000fc80` | 2808 | `block_state_root` | UNCONVERTED |
| `0x8000fde0` | `0x8001001c` | 572 | `chain_config_valid` | UNCONVERTED |
| `0x8001001c` | `0x80010188` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80010188` | `0x8001019c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x8001019c` | `0x800101a8` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800101a8` | `0x800101f8` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800101f8` | `0x80010218` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80010218` | `0x8001027c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x8001027c` | `0x80010524` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80010524` | `0x80010778` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80010778` | `0x8001092c` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x8001092c` | `0x80010d38` | 1036 | `log_records_encode_rlp` | UNCONVERTED |
| `0x800114a4` | `0x8001169c` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800119bc` | `0x80011be8` | 556 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80011ce4` | `0x8001aaa0` | 36284 | `block_verdict` | UNCONVERTED |
| `0x8001b3bc` | `0x8001b614` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001b614` | `0x8001b88c` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001b88c` | `0x8001bb20` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001c1ec` | `0x8001c834` | 1608 | `bal_code_preimages_valid` | UNCONVERTED |
| `0x8001c834` | `0x8001c8c4` | 144 | `bbcv_addr_is_system_contract` | UNCONVERTED |
| `0x8001c8c4` | `0x8001c900` | 60 | `bbcv_addr_eq20` | UNCONVERTED |
| `0x8001c900` | `0x8001ca4c` | 332 | `bal_addr_is_tx_sender` | UNCONVERTED |
| `0x8001ca4c` | `0x8001cb50` | 260 | `bal_codes_contains_push20_extcodehash` | UNCONVERTED |
| `0x8001cb50` | `0x8001cc5c` | 268 | `bal_codes_contains_push20_code_read` | UNCONVERTED |
| `0x8001cc5c` | `0x8001cdac` | 336 | `bal_codes_contains_push20_balance` | UNCONVERTED |
| `0x8001cdac` | `0x8001ceb0` | 260 | `bal_codes_contains_push20_selfdestruct` | UNCONVERTED |
| `0x8001ceb0` | `0x8001cfa8` | 248 | `bal_codes_contains_address_selfdestruct` | UNCONVERTED |
| `0x8001cfa8` | `0x8001d0dc` | 308 | `bal_codes_contains_push20_call_target` | UNCONVERTED |
| `0x8001d0dc` | `0x8001d1d0` | 244 | `bal_codes_contains_delegation_marker_target` | UNCONVERTED |
| `0x8001d1d0` | `0x8001d3d0` | 512 | `bal_call_target_delegated_code_valid` | UNCONVERTED |
| `0x8001d3d0` | `0x8001d4c0` | 240 | `bbcv_bal_contains_addr` | UNCONVERTED |
| `0x8001d4c0` | `0x8001d7b8` | 760 | `bal_same_block_delegation_code_resolve` | UNCONVERTED |
| `0x8001d7b8` | `0x8001d9ac` | 500 | `bal_txs_contains_push20_selfdestruct` | UNCONVERTED |
| `0x8001d9ac` | `0x8001dda0` | 1012 | `bal_txs_contains_create_collision_touch` | UNCONVERTED |
| `0x8001dda0` | `0x8001e118` | 888 | `bal_txs_contains_top_create2_collision_touch` | UNCONVERTED |
| `0x8001e118` | `0x8001e29c` | 388 | `bal_tx_initcode_contains_create2_target` | UNCONVERTED |
| `0x8001e29c` | `0x8001e4b4` | 536 | `bal_contains_internal_create_collision_touch` | UNCONVERTED |
| `0x8001e4b4` | `0x8001e69c` | 488 | `bal_contains_internal_create2_collision_touch` | UNCONVERTED |
| `0x8001e69c` | `0x8001e7f8` | 348 | `bal_codes_find_create2_push4_salt` | UNCONVERTED |
| `0x8001e7f8` | `0x8001e92c` | 308 | `bal_try_create2_initcodes` | UNCONVERTED |
| `0x8001e92c` | `0x8001e9f4` | 200 | `bal_codes_contains_create_opcode` | UNCONVERTED |
| `0x8001f004` | `0x8001f168` | 356 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001f168` | `0x8001f2fc` | 404 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001f2fc` | `0x8001f4b8` | 444 | `block_verdict_single_tx_creation_runtime` | UNCONVERTED |
| `0x8001f7bc` | `0x8001f804` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001f938` | `0x8001fb08` | 464 | `bal_recipient_storage_keys` | UNCONVERTED |
| `0x8001fb08` | `0x8001fc90` | 392 | `bal_recipient_storage_reads_keys` | UNCONVERTED |
| `0x8001fc90` | `0x80020048` | 952 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x80020048` | `0x800201c8` | 384 | `bv_emit_single_tx_tl7708` | UNCONVERTED |
| `0x800201c8` | `0x8002110c` | 3908 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x800219e0` | `0x80021af4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x80021af4` | `0x80021dfc` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x80022778` | `0x800228cc` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x80022c94` | `0x80022cd4` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80022cd4` | `0x80023210` | 1340 | `seed_callee_storage` | UNCONVERTED |
| `0x80023210` | `0x80023470` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x80023470` | `0x800236f8` | 648 | `bal_storage_matches_exec_log` | UNCONVERTED |
| `0x800236f8` | `0x80023c8c` | 1428 | `bal_storage_covers_exec_log` | UNCONVERTED |
| `0x80023c8c` | `0x80023c94` | 8 | `bal_all_accounts_storage_consistent` | UNCONVERTED |
| `0x80023c94` | `0x80023e30` | 412 | `bal_all_accounts_storage_consistent_skip_list` | UNCONVERTED |
| `0x80023e30` | `0x8002412c` | 764 | `bal_slot_tuple_sequence` | UNCONVERTED |
| `0x8002412c` | `0x80024424` | 760 | `exec_log_slot_tuples` | UNCONVERTED |
| `0x80024424` | `0x80024710` | 748 | `system_user_exec_log_slot_tuples` | UNCONVERTED |
| `0x80024c4c` | `0x80024ef0` | 676 | `account_tuple_sequences_consistent` | UNCONVERTED |
| `0x80024ef0` | `0x80024ef8` | 8 | `bal_all_accounts_tuple_sequences_consistent` | UNCONVERTED |
| `0x80024ef8` | `0x80025068` | 368 | `bal_all_accounts_tuple_sequences_consistent_skip_list` | UNCONVERTED |
| `0x80025068` | `0x80025224` | 444 | `bal_storage_reads_in_exec_log` | UNCONVERTED |
| `0x80025494` | `0x8002558c` | 248 | `stage_blockhash_m29` | UNCONVERTED |
| `0x8002578c` | `0x800259c4` | 568 | `bal_all_accounts_nonstorage_consistent` | UNCONVERTED |
| `0x80026000` | `0x80026100` | 256 | `bti_scan_tuples` | UNCONVERTED |
| `0x800261c0` | `0x80026388` | 456 | `bal_txs_independent` | UNCONVERTED |
| `0x80026388` | `0x800265b8` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x800265b8` | `0x800265f4` | 60 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x800265f4` | `0x80026820` | 556 | `tx_intrinsic_state_gas` | UNCONVERTED |
| `0x80026820` | `0x80026c54` | 1076 | `block_verdict_receipt_gas_eip8037_adjust` | UNCONVERTED |
| `0x80026c54` | `0x80026fe8` | 916 | `block_verdict_failed_type4_auth_regular_adjust` | UNCONVERTED |
| `0x800272cc` | `0x800274e4` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x800274e4` | `0x800276d8` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80027a6c` | `0x800280c0` | 1620 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800280c0` | `0x8002840c` | 844 | `simple_transfer_recipient_bal_verify` | UNCONVERTED |
| `0x8002840c` | `0x80028798` | 908 | `simple_transfer_fee_recipient_bal_verify` | UNCONVERTED |
| `0x80028af8` | `0x80028e70` | 888 | `eip8037_state_used_before_tx` | UNCONVERTED |
| `0x80028e70` | `0x80028f1c` | 172 | `eip8037_prior_state_used_exact` | UNCONVERTED |
| `0x80028f1c` | `0x80029744` | 2088 | `eip8037_tx_gas_gate` | UNCONVERTED |
| `0x800297ac` | `0x80029844` | 152 | `multi_tx_actual_sender_debit` | UNCONVERTED |
| `0x80029844` | `0x8002997c` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x8002997c` | `0x800299e0` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x800299e0` | `0x8002a000` | 1568 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x8002a060` | `0x8002a11c` | 188 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x8002a488` | `0x8002a5e0` | 344 | `eip7702_authorization_extract_signature` | UNCONVERTED |
| `0x8002a798` | `0x8002a928` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x8002a928` | `0x8002b200` | 2264 | `tx_eip7702_existing_authority_refund` | UNCONVERTED |
| `0x8002b200` | `0x8002b6ac` | 1196 | `eip7702_auth_nonstorage_effects` | UNCONVERTED |
| `0x8002ba20` | `0x8002bcbc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002bcbc` | `0x8002bcf4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c6ac` | `0x8002c840` | 404 | `tx_legacy_extract_signature` | UNCONVERTED |
| `0x8002c840` | `0x8002c9fc` | 444 | `tx_eip2930_extract_signature` | UNCONVERTED |
| `0x8002c9fc` | `0x8002cbcc` | 464 | `tx_eip1559_extract_signature` | UNCONVERTED |
| `0x8002cbcc` | `0x8002cdc4` | 504 | `tx_eip4844_extract_signature` | UNCONVERTED |
| `0x8002cdc4` | `0x8002cfa8` | 484 | `tx_eip7702_extract_signature` | UNCONVERTED |
| `0x8002da20` | `0x8002e704` | 3300 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002e704` | `0x8002e88c` | 392 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002e88c` | `0x8002e900` | 116 | `.preload_expand_loop` | UNCONVERTED |
| `0x8002e900` | `0x8002e934` | 52 | `.preload_expand_done` | UNCONVERTED |
| `0x8002e934` | `0x8002e944` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002e944` | `0x8002e978` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002e978` | `0x8002e990` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002e990` | `0x8002e9a0` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002e9a0` | `0x8002e9d4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002e9d4` | `0x8002e9dc` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002e9dc` | `0x8002ea28` | 76 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ea28` | `0x8002ea58` | 48 | `.retag_preload_loop` | UNCONVERTED |
| `0x8002ea58` | `0x8002ea94` | 60 | `.retag_preload_done` | UNCONVERTED |
| `0x8002ea94` | `0x8002eaa0` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002eaa0` | `0x8002eab8` | 24 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002eab8` | `0x8002eac0` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002eac0` | `0x8002eacc` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002eacc` | `0x8002eae4` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002eae4` | `0x8002eafc` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002eafc` | `0x8002eb10` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002eb10` | `0x8002eb2c` | 28 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002eb2c` | `0x8002eb40` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002eb40` | `0x8002eb88` | 72 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002eb88` | `0x8002ebac` | 36 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002ebac` | `0x8002ebac` | 0 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002ebac` | `0x8002edb0` | 516 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002edb0` | `0x8002edbc` | 12 | `.jdbm_len_ok` | UNCONVERTED |
| `0x8002edbc` | `0x8002edf8` | 60 | `.jdbm_scan` | UNCONVERTED |
| `0x8002edf8` | `0x8002ee24` | 44 | `.jdbm_not_jumpdest` | UNCONVERTED |
| `0x8002ee24` | `0x8002ee30` | 12 | `.jdbm_push` | UNCONVERTED |
| `0x8002ee30` | `0x8002ee50` | 32 | `.jdbm_dupn_swapn` | UNCONVERTED |
| `0x8002ee50` | `0x8002ee6c` | 28 | `.jdbm_exchange` | UNCONVERTED |
| `0x8002ee6c` | `0x8002ee74` | 8 | `.jdbm_skip_eip8024_imm` | UNCONVERTED |
| `0x8002ee74` | `0x8002ee7c` | 8 | `.jdbm_plain` | UNCONVERTED |
| `0x8002ee7c` | `0x8002eeb0` | 52 | `.jdbm_done` | UNCONVERTED |
| `0x8002eeb0` | `0x8002ef50` | 160 | `.dispatch_loop` | UNCONVERTED |
| `0x8002ef50` | `0x8002f0a4` | 340 | `balance_at_header_state_root` | UNCONVERTED |
| `0x8002ff30` | `0x8002ff58` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x8002ff58` | `0x80030078` | 288 | `create_record_code_effect` | UNCONVERTED |
| `0x800300d8` | `0x800301f4` | 284 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800301f4` | `0x80030244` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80030244` | `0x80030294` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80030294` | `0x800302c4` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x800302c4` | `0x80030308` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80030308` | `0x8003034c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x8003034c` | `0x800303fc` | 176 | `modexp_mul` | UNCONVERTED |
| `0x800303fc` | `0x80030558` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80030558` | `0x80030858` | 768 | `zkvm_modexp` | UNCONVERTED |
| `0x80030858` | `0x80031058` | 2048 | `modexp_bn_base` | UNCONVERTED |
| `0x80031058` | `0x80031858` | 2048 | `modexp_bn_exp` | UNCONVERTED |
| `0x80031858` | `0x80032058` | 2048 | `modexp_bn_mod` | UNCONVERTED |
| `0x80032058` | `0x80032858` | 2048 | `modexp_bn_result` | UNCONVERTED |
| `0x80032858` | `0x80033858` | 4096 | `modexp_bn_product` | UNCONVERTED |
| `0x80033858` | `0x80034060` | 2056 | `modexp_bn_remainder` | UNCONVERTED |
| `0x80034060` | `0x8003423c` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8003423c` | `0x800342e8` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800342e8` | `0x80034460` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80034460` | `0x80034620` | 448 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80034620` | `0x80034788` | 360 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80034800` | `0x800348dc` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800348dc` | `0x80034a2c` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80034a2c` | `0x80034c08` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80034db8` | `0x80034f9c` | 484 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80034f9c` | `0x80034ff0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80034ff0` | `0x80035038` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80035038` | `0x8003510c` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x8003510c` | `0x80035230` | 292 | `dispatcher_seed_pending_upfront_balance` | UNCONVERTED |
| `0x800358b0` | `0x8003598c` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x8003598c` | `0x80035afc` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80035b2c` | `0x80035ba8` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80035ba8` | `0x80035c94` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800362f8` | `0x80036368` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80036368` | `0x800363c8` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x8003673c` | `0x800368cc` | 400 | `bnq_mul` | UNCONVERTED |
| `0x800368cc` | `0x80036920` | 84 | `bnq_add` | UNCONVERTED |
| `0x80036920` | `0x80036974` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80036b3c` | `0x80036da8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80036da8` | `0x800370e8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800370e8` | `0x80037398` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80037398` | `0x800376cc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800376cc` | `0x80037a54` | 904 | `bng2_add` | UNCONVERTED |
| `0x80037a54` | `0x80037b74` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80037b94` | `0x80037fc4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80037fc4` | `0x80038408` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003845c` | `0x80038608` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80038728` | `0x800388f0` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80038a7c` | `0x80038c40` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800393d0` | `0x800396a8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80039a7c` | `0x80039b8c` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80039b8c` | `0x80039ce0` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80039ce0` | `0x80039e18` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80039f94` | `0x8003a024` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003a024` | `0x8003a0f4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x8003a0f4` | `0x8003a2cc` | 472 | `blq_mul` | UNCONVERTED |
| `0x8003a2cc` | `0x8003a328` | 92 | `blq_add` | UNCONVERTED |
| `0x8003a328` | `0x8003a384` | 92 | `blq_sub` | UNCONVERTED |
| `0x8003a574` | `0x8003a7e0` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003a7e0` | `0x8003ab00` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003ab00` | `0x8003adb0` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003adb0` | `0x8003af8c` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x8003af8c` | `0x8003b2d4` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x8003b420` | `0x8003cc84` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003cc84` | `0x8003dec0` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003df44` | `0x8003df9c` | 88 | `call_frame_enter` | UNCONVERTED |
| `0x8003df9c` | `0x8003e0b8` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003e0c8` | `0x8003e0f8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003e0f8` | `0x8003e5a8` | 1200 | `call_frame_descend` | UNCONVERTED |
| `0x8003e5a8` | `0x8003e698` | 240 | `create_frame_descend` | UNCONVERTED |
| `0x8003e698` | `0x8003e7b8` | 288 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003e848` | `0x8003eb30` | 744 | `nonstorage_effect_aggregate` | UNCONVERTED |
| `0x8003eb30` | `0x8003eee4` | 948 | `frame_return` | UNCONVERTED |
| `0x8003eee4` | `0x8003ef14` | 48 | `h_PUSH0` | UNCONVERTED |
| `0x8003ef14` | `0x8003ef4c` | 56 | `h_PUSH1` | UNCONVERTED |
| `0x8003ef4c` | `0x8003ef8c` | 64 | `h_PUSH2` | UNCONVERTED |
| `0x8003ef8c` | `0x8003efd4` | 72 | `h_PUSH3` | UNCONVERTED |
| `0x8003efd4` | `0x8003f024` | 80 | `h_PUSH4` | UNCONVERTED |
| `0x8003f024` | `0x8003f07c` | 88 | `h_PUSH5` | UNCONVERTED |
| `0x8003f07c` | `0x8003f0dc` | 96 | `h_PUSH6` | UNCONVERTED |
| `0x8003f0dc` | `0x8003f144` | 104 | `h_PUSH7` | UNCONVERTED |
| `0x8003f144` | `0x8003f1b4` | 112 | `h_PUSH8` | UNCONVERTED |
| `0x8003f1b4` | `0x8003f22c` | 120 | `h_PUSH9` | UNCONVERTED |
| `0x8003f22c` | `0x8003f2ac` | 128 | `h_PUSH10` | UNCONVERTED |
| `0x8003f2ac` | `0x8003f334` | 136 | `h_PUSH11` | UNCONVERTED |
| `0x8003f334` | `0x8003f3c4` | 144 | `h_PUSH12` | UNCONVERTED |
| `0x8003f3c4` | `0x8003f45c` | 152 | `h_PUSH13` | UNCONVERTED |
| `0x8003f45c` | `0x8003f4fc` | 160 | `h_PUSH14` | UNCONVERTED |
| `0x8003f4fc` | `0x8003f5a4` | 168 | `h_PUSH15` | UNCONVERTED |
| `0x8003f5a4` | `0x8003f654` | 176 | `h_PUSH16` | UNCONVERTED |
| `0x8003f654` | `0x8003f70c` | 184 | `h_PUSH17` | UNCONVERTED |
| `0x8003f70c` | `0x8003f7cc` | 192 | `h_PUSH18` | UNCONVERTED |
| `0x8003f7cc` | `0x8003f894` | 200 | `h_PUSH19` | UNCONVERTED |
| `0x8003f894` | `0x8003f964` | 208 | `h_PUSH20` | UNCONVERTED |
| `0x8003f964` | `0x8003fa3c` | 216 | `h_PUSH21` | UNCONVERTED |
| `0x8003fa3c` | `0x8003fb1c` | 224 | `h_PUSH22` | UNCONVERTED |
| `0x8003fb1c` | `0x8003fc04` | 232 | `h_PUSH23` | UNCONVERTED |
| `0x8003fc04` | `0x8003fcf4` | 240 | `h_PUSH24` | UNCONVERTED |
| `0x8003fcf4` | `0x8003fdec` | 248 | `h_PUSH25` | UNCONVERTED |
| `0x8003fdec` | `0x8003feec` | 256 | `h_PUSH26` | UNCONVERTED |
| `0x8003feec` | `0x8003fff4` | 264 | `h_PUSH27` | UNCONVERTED |
| `0x8003fff4` | `0x80040104` | 272 | `h_PUSH28` | UNCONVERTED |
| `0x80040104` | `0x8004021c` | 280 | `h_PUSH29` | UNCONVERTED |
| `0x8004021c` | `0x8004033c` | 288 | `h_PUSH30` | UNCONVERTED |
| `0x8004033c` | `0x80040464` | 296 | `h_PUSH31` | UNCONVERTED |
| `0x80040464` | `0x80040594` | 304 | `h_PUSH32` | UNCONVERTED |
| `0x80040594` | `0x800405ec` | 88 | `h_DUP1` | UNCONVERTED |
| `0x800405ec` | `0x80040644` | 88 | `h_DUP2` | UNCONVERTED |
| `0x80040644` | `0x8004069c` | 88 | `h_DUP3` | UNCONVERTED |
| `0x8004069c` | `0x800406f4` | 88 | `h_DUP4` | UNCONVERTED |
| `0x800406f4` | `0x8004074c` | 88 | `h_DUP5` | UNCONVERTED |
| `0x8004074c` | `0x800407a4` | 88 | `h_DUP6` | UNCONVERTED |
| `0x800407a4` | `0x800407fc` | 88 | `h_DUP7` | UNCONVERTED |
| `0x800407fc` | `0x80040854` | 88 | `h_DUP8` | UNCONVERTED |
| `0x80040854` | `0x800408ac` | 88 | `h_DUP9` | UNCONVERTED |
| `0x800408ac` | `0x80040904` | 88 | `h_DUP10` | UNCONVERTED |
| `0x80040904` | `0x8004095c` | 88 | `h_DUP11` | UNCONVERTED |
| `0x8004095c` | `0x800409b4` | 88 | `h_DUP12` | UNCONVERTED |
| `0x800409b4` | `0x80040a0c` | 88 | `h_DUP13` | UNCONVERTED |
| `0x80040a0c` | `0x80040a64` | 88 | `h_DUP14` | UNCONVERTED |
| `0x80040a64` | `0x80040abc` | 88 | `h_DUP15` | UNCONVERTED |
| `0x80040abc` | `0x80040b14` | 88 | `h_DUP16` | UNCONVERTED |
| `0x80040b14` | `0x80040b74` | 96 | `h_SWAP1` | UNCONVERTED |
| `0x80040b74` | `0x80040bd4` | 96 | `h_SWAP2` | UNCONVERTED |
| `0x80040bd4` | `0x80040c34` | 96 | `h_SWAP3` | UNCONVERTED |
| `0x80040c34` | `0x80040c94` | 96 | `h_SWAP4` | UNCONVERTED |
| `0x80040c94` | `0x80040cf4` | 96 | `h_SWAP5` | UNCONVERTED |
| `0x80040cf4` | `0x80040d54` | 96 | `h_SWAP6` | UNCONVERTED |
| `0x80040d54` | `0x80040db4` | 96 | `h_SWAP7` | UNCONVERTED |
| `0x80040db4` | `0x80040e14` | 96 | `h_SWAP8` | UNCONVERTED |
| `0x80040e14` | `0x80040e74` | 96 | `h_SWAP9` | UNCONVERTED |
| `0x80040e74` | `0x80040ed4` | 96 | `h_SWAP10` | UNCONVERTED |
| `0x80040ed4` | `0x80040f34` | 96 | `h_SWAP11` | UNCONVERTED |
| `0x80040f34` | `0x80040f94` | 96 | `h_SWAP12` | UNCONVERTED |
| `0x80040f94` | `0x80040ff4` | 96 | `h_SWAP13` | UNCONVERTED |
| `0x80040ff4` | `0x80041054` | 96 | `h_SWAP14` | UNCONVERTED |
| `0x80041054` | `0x800410b4` | 96 | `h_SWAP15` | UNCONVERTED |
| `0x800410b4` | `0x80041114` | 96 | `h_SWAP16` | UNCONVERTED |
| `0x80041114` | `0x8004112c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8004112c` | `0x80041140` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80041140` | `0x800411ac` | 108 | `.dupn_imm_valid` | UNCONVERTED |
| `0x800411ac` | `0x800411c4` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800411c4` | `0x800411d8` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800411d8` | `0x80041250` | 120 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80041250` | `0x80041268` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80041268` | `0x8004127c` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8004127c` | `0x8004129c` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8004129c` | `0x800412a4` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x800412a4` | `0x800412b0` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x800412b0` | `0x800412b4` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800412b4` | `0x80041328` | 116 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80041328` | `0x800413c0` | 152 | `h_ADD` | UNCONVERTED |
| `0x800413c0` | `0x800414e4` | 292 | `h_MUL` | UNCONVERTED |
| `0x800414e4` | `0x8004157c` | 152 | `h_SUB` | UNCONVERTED |
| `0x8004157c` | `0x80041664` | 232 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80041664` | `0x800416ec` | 136 | `h_LT` | UNCONVERTED |
| `0x800416ec` | `0x80041774` | 136 | `h_GT` | UNCONVERTED |
| `0x80041774` | `0x800417f8` | 132 | `h_SLT` | UNCONVERTED |
| `0x800417f8` | `0x8004187c` | 132 | `h_SGT` | UNCONVERTED |
| `0x8004187c` | `0x800418f0` | 116 | `h_EQ` | UNCONVERTED |
| `0x800418f0` | `0x80041940` | 80 | `h_ISZERO` | UNCONVERTED |
| `0x80041940` | `0x800419a4` | 100 | `h_AND` | UNCONVERTED |
| `0x800419a4` | `0x80041a08` | 100 | `h_OR` | UNCONVERTED |
| `0x80041a08` | `0x80041a6c` | 100 | `h_XOR` | UNCONVERTED |
| `0x80041a6c` | `0x80041abc` | 80 | `h_NOT` | UNCONVERTED |
| `0x80041abc` | `0x80041b98` | 220 | `h_BYTE` | UNCONVERTED |
| `0x80041b98` | `0x80041d28` | 400 | `h_SHL` | UNCONVERTED |
| `0x80041d28` | `0x80041eb8` | 400 | `h_SHR` | UNCONVERTED |
| `0x80041eb8` | `0x8004205c` | 420 | `h_SAR` | UNCONVERTED |
| `0x8004205c` | `0x8004214c` | 240 | `h_CLZ` | UNCONVERTED |
| `0x8004214c` | `0x80042170` | 36 | `h_POP` | UNCONVERTED |
| `0x80042170` | `0x800423c0` | 592 | `h_MLOAD` | UNCONVERTED |
| `0x800423c0` | `0x800425b4` | 500 | `h_MSTORE` | UNCONVERTED |
| `0x800425b4` | `0x800426a0` | 236 | `h_MSTORE8` | UNCONVERTED |
| `0x800426a0` | `0x800426d4` | 52 | `h_MSIZE` | UNCONVERTED |
| `0x800426d4` | `0x80042708` | 52 | `h_GAS` | UNCONVERTED |
| `0x80042708` | `0x80042748` | 64 | `h_ADDRESS` | UNCONVERTED |
| `0x80042748` | `0x80042788` | 64 | `h_ORIGIN` | UNCONVERTED |
| `0x80042788` | `0x800427c8` | 64 | `h_CALLER` | UNCONVERTED |
| `0x800427c8` | `0x80042808` | 64 | `h_CALLVALUE` | UNCONVERTED |
| `0x80042808` | `0x80042848` | 64 | `h_GASPRICE` | UNCONVERTED |
| `0x80042848` | `0x80042888` | 64 | `h_COINBASE` | UNCONVERTED |
| `0x80042888` | `0x800428c8` | 64 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800428c8` | `0x80042908` | 64 | `h_NUMBER` | UNCONVERTED |
| `0x80042908` | `0x80042948` | 64 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80042948` | `0x80042988` | 64 | `h_GASLIMIT` | UNCONVERTED |
| `0x80042988` | `0x800429c8` | 64 | `h_CHAINID` | UNCONVERTED |
| `0x800429c8` | `0x80042a08` | 64 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042a08` | `0x80042a48` | 64 | `h_BASEFEE` | UNCONVERTED |
| `0x80042a48` | `0x80042a88` | 64 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042a88` | `0x80042ac8` | 64 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042ac8` | `0x80042b54` | 140 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042b54` | `0x80042bf0` | 156 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042bf0` | `0x80042c24` | 52 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042c24` | `0x80042e28` | 516 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042e28` | `0x80042f88` | 352 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042f88` | `0x80042fbc` | 52 | `h_CODESIZE` | UNCONVERTED |
| `0x80042fbc` | `0x800430ec` | 304 | `h_CODECOPY` | UNCONVERTED |
| `0x800430ec` | `0x800430f4` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800430f4` | `0x800431a4` | 176 | `h_JUMP` | UNCONVERTED |
| `0x800431a4` | `0x80043288` | 228 | `h_JUMPI` | UNCONVERTED |
| `0x80043288` | `0x800432bc` | 52 | `h_PC` | UNCONVERTED |
| `0x800432bc` | `0x80043508` | 588 | `h_KECCAK256` | UNCONVERTED |
| `0x80043508` | `0x800437b4` | 684 | `h_LOG0` | UNCONVERTED |
| `0x800437b4` | `0x80043a80` | 716 | `h_LOG1` | UNCONVERTED |
| `0x80043a80` | `0x80043d6c` | 748 | `h_LOG2` | UNCONVERTED |
| `0x80043d6c` | `0x80044078` | 780 | `h_LOG3` | UNCONVERTED |
| `0x80044078` | `0x800443a4` | 812 | `h_LOG4` | UNCONVERTED |
| `0x800443a4` | `0x8004462c` | 648 | `h_BALANCE` | UNCONVERTED |
| `0x8004462c` | `0x8004488c` | 608 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8004488c` | `0x80044d1c` | 1168 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044d1c` | `0x800451a8` | 1164 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800451a8` | `0x800452c8` | 288 | `h_SLOAD` | UNCONVERTED |
| `0x800452c8` | `0x80045738` | 1136 | `h_SSTORE` | UNCONVERTED |
| `0x80045738` | `0x80045814` | 220 | `h_TLOAD` | UNCONVERTED |
| `0x80045814` | `0x800458d4` | 192 | `h_TSTORE` | UNCONVERTED |
| `0x800458d4` | `0x80045b08` | 564 | `h_MCOPY` | UNCONVERTED |
| `0x80045b08` | `0x80045f9c` | 1172 | `h_RETURN` | UNCONVERTED |
| `0x80045f9c` | `0x80046214` | 632 | `h_REVERT` | UNCONVERTED |
| `0x80046214` | `0x80046218` | 4 | `h_INVALID` | UNCONVERTED |
| `0x80046218` | `0x80047048` | 3632 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047048` | `0x80047084` | 60 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047084` | `0x800471b8` | 308 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800471b8` | `0x80047b24` | 2412 | `h_CREATE` | UNCONVERTED |
| `0x80047b24` | `0x8004b9b0` | 16012 | `h_CALL` | UNCONVERTED |
| `0x8004b9b0` | `0x8004ebb0` | 12800 | `h_CALLCODE` | UNCONVERTED |
| `0x8004ebb0` | `0x80051a70` | 11968 | `h_DELEGATECALL` | UNCONVERTED |
| `0x80051a70` | `0x8005241c` | 2476 | `h_CREATE2` | UNCONVERTED |
| `0x8005241c` | `0x80055454` | 12344 | `h_STATICCALL` | UNCONVERTED |
| `0x80055454` | `0x80055cfc` | 2216 | `h_MULMOD` | UNCONVERTED |
| `0x80055cfc` | `0x800565e0` | 2276 | `h_DIV` | UNCONVERTED |
| `0x800565e0` | `0x80056b6c` | 1420 | `h_MOD` | UNCONVERTED |
| `0x80056b6c` | `0x80057208` | 1692 | `h_SDIV` | UNCONVERTED |
| `0x80057208` | `0x80057220` | 24 | `h_SDIV_done` | UNCONVERTED |
| `0x80057220` | `0x800578bc` | 1692 | `h_SMOD` | UNCONVERTED |
| `0x800578bc` | `0x800578d4` | 24 | `h_SMOD_done` | UNCONVERTED |
| `0x800578d4` | `0x800581e8` | 2324 | `h_ADDMOD` | UNCONVERTED |
| `0x800581e8` | `0x80058518` | 816 | `h_EXP` | UNCONVERTED |
| `0x80058518` | `0x80058564` | 76 | `h_STOP` | UNCONVERTED |
| `0x80058564` | `0x80058568` | 4 | `h_invalid` | UNCONVERTED |
| `0x80058568` | `0x80058590` | 40 | `.exit_static_violation` | UNCONVERTED |
| `0x80058590` | `0x800585e4` | 84 | `.exit_invalid` | UNCONVERTED |
| `0x800585e4` | `0x8005860c` | 40 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005860c` | `0x80058660` | 84 | `.exit_invalid_op` | UNCONVERTED |
| `0x80058660` | `0x80058688` | 40 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80058688` | `0x800586ac` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x800586ac` | `0x800586d4` | 40 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x800586d4` | `0x80058728` | 84 | `.exit_outofgas` | UNCONVERTED |
| `0x80058728` | `0x80058750` | 40 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80058750` | `0x800587a4` | 84 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800587a4` | `0x800587cc` | 40 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800587cc` | `0x80058820` | 84 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80058820` | `0x80058848` | 40 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80058848` | `0x80058848` | 0 | `.exit_label` | UNCONVERTED |
| `0x80058848` | `0x80058864` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80058864` | `0x80058974` | 272 | `derive_block_system_requests` | UNCONVERTED |
| `0x800589ac` | `0x80058a78` | 204 | `stage_system_call` | UNCONVERTED |
| `0x80058a78` | `0x80058c18` | 416 | `stage_system_call_payload` | UNCONVERTED |
| `0x80058c18` | `0x80058d18` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x80058d18` | `0x80058e48` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80058e48` | `0x80058ea4` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80058ea4` | `0x80058ec4` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80058ec4` | `0x80059000` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80059000` | `0x8005909c` | 156 | `assemble_execution_requests` | UNCONVERTED |
| `0x8005912c` | `0x80059418` | 748 | `stage_predeploy_storage_preload` | UNCONVERTED |
