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

`.text` = [0x80000000, 0x80054a88), 346760 bytes (`RegionMap.textSizeBytes = 0x54a88`)
- symbols in `.text`: 800 (358 converted, 442 unconverted)
- covered by converted `_prog`s: 86924 bytes (25.07%)
- NOT covered: 259836 bytes (74.93%), 442 ranges

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
| `0x8000ed94` | `0x8000ef8c` | 504 | `capture_system_storage_exec_rows` | UNCONVERTED |
| `0x8000ef8c` | `0x8000f174` | 488 | `append_modeled_system_storage_tuple_rows` | UNCONVERTED |
| `0x8000f174` | `0x8000fc6c` | 2808 | `block_state_root` | UNCONVERTED |
| `0x8000fdcc` | `0x80010008` | 572 | `chain_config_valid` | UNCONVERTED |
| `0x80010008` | `0x80010174` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80010174` | `0x80010188` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80010188` | `0x80010194` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80010194` | `0x800101e4` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800101e4` | `0x80010204` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80010204` | `0x80010268` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80010268` | `0x80010510` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80010510` | `0x80010764` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80010764` | `0x80010918` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80010918` | `0x80010d24` | 1036 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80011490` | `0x80011688` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800119a8` | `0x80011bd4` | 556 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80011cd0` | `0x80012018` | 840 | `simple_transfer_intrinsic_gas` | UNCONVERTED |
| `0x80012018` | `0x800180cc` | 24756 | `block_verdict` | UNCONVERTED |
| `0x800189e8` | `0x80018c40` | 600 | `tx_extract_to_address` | CONVERTED (`txExtractToAddress_prog`, 150) |
| `0x80018c40` | `0x80018eb8` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x80018eb8` | `0x8001914c` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x80019818` | `0x80019e60` | 1608 | `bal_code_preimages_valid` | UNCONVERTED |
| `0x80019e60` | `0x80019ef0` | 144 | `bbcv_addr_is_system_contract` | UNCONVERTED |
| `0x80019ef0` | `0x80019f2c` | 60 | `bbcv_addr_eq20` | UNCONVERTED |
| `0x80019f2c` | `0x8001a078` | 332 | `bal_addr_is_tx_sender` | UNCONVERTED |
| `0x8001a078` | `0x8001a17c` | 260 | `bal_codes_contains_push20_extcodehash` | UNCONVERTED |
| `0x8001a17c` | `0x8001a288` | 268 | `bal_codes_contains_push20_code_read` | UNCONVERTED |
| `0x8001a288` | `0x8001a3d8` | 336 | `bal_codes_contains_push20_balance` | UNCONVERTED |
| `0x8001a3d8` | `0x8001a4dc` | 260 | `bal_codes_contains_push20_selfdestruct` | UNCONVERTED |
| `0x8001a4dc` | `0x8001a5d4` | 248 | `bal_codes_contains_address_selfdestruct` | UNCONVERTED |
| `0x8001a5d4` | `0x8001a708` | 308 | `bal_codes_contains_push20_call_target` | UNCONVERTED |
| `0x8001a708` | `0x8001a7fc` | 244 | `bal_codes_contains_delegation_marker_target` | UNCONVERTED |
| `0x8001a7fc` | `0x8001a9fc` | 512 | `bal_call_target_delegated_code_valid` | UNCONVERTED |
| `0x8001a9fc` | `0x8001aaec` | 240 | `bbcv_bal_contains_addr` | UNCONVERTED |
| `0x8001aaec` | `0x8001ae5c` | 880 | `bal_same_block_delegation_code_resolve` | UNCONVERTED |
| `0x8001ae5c` | `0x8001b050` | 500 | `bal_txs_contains_push20_selfdestruct` | UNCONVERTED |
| `0x8001b050` | `0x8001b444` | 1012 | `bal_txs_contains_create_collision_touch` | UNCONVERTED |
| `0x8001b444` | `0x8001b7bc` | 888 | `bal_txs_contains_top_create2_collision_touch` | UNCONVERTED |
| `0x8001b7bc` | `0x8001b940` | 388 | `bal_tx_initcode_contains_create2_target` | UNCONVERTED |
| `0x8001b940` | `0x8001bb58` | 536 | `bal_contains_internal_create_collision_touch` | UNCONVERTED |
| `0x8001bb58` | `0x8001bd40` | 488 | `bal_contains_internal_create2_collision_touch` | UNCONVERTED |
| `0x8001bd40` | `0x8001be9c` | 348 | `bal_codes_find_create2_push4_salt` | UNCONVERTED |
| `0x8001be9c` | `0x8001bfd0` | 308 | `bal_try_create2_initcodes` | UNCONVERTED |
| `0x8001bfd0` | `0x8001c098` | 200 | `bal_codes_contains_create_opcode` | UNCONVERTED |
| `0x8001c6a8` | `0x8001c80c` | 356 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001c80c` | `0x8001c9a0` | 404 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001c9a0` | `0x8001ccac` | 780 | `block_verdict_single_tx_creation_runtime` | UNCONVERTED |
| `0x8001cfb0` | `0x8001cff8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d12c` | `0x8001d2fc` | 464 | `bal_recipient_storage_keys` | UNCONVERTED |
| `0x8001d2fc` | `0x8001d484` | 392 | `bal_recipient_storage_reads_keys` | UNCONVERTED |
| `0x8001d484` | `0x8001d83c` | 952 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001d83c` | `0x8001d9bc` | 384 | `bv_emit_single_tx_tl7708` | UNCONVERTED |
| `0x8001d9bc` | `0x8001ea84` | 4296 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f358` | `0x8001f46c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f46c` | `0x8001f774` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x800200f0` | `0x80020244` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8002060c` | `0x8002064c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8002064c` | `0x80020b88` | 1340 | `seed_callee_storage` | UNCONVERTED |
| `0x80020b88` | `0x80020de8` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x80020de8` | `0x80021070` | 648 | `bal_storage_matches_exec_log` | UNCONVERTED |
| `0x80021070` | `0x80021604` | 1428 | `bal_storage_covers_exec_log` | UNCONVERTED |
| `0x80021604` | `0x8002160c` | 8 | `bal_all_accounts_storage_consistent` | UNCONVERTED |
| `0x8002160c` | `0x800217a8` | 412 | `bal_all_accounts_storage_consistent_skip_list` | UNCONVERTED |
| `0x800217a8` | `0x80021aa4` | 764 | `bal_slot_tuple_sequence` | UNCONVERTED |
| `0x80021aa4` | `0x80021d9c` | 760 | `exec_log_slot_tuples` | UNCONVERTED |
| `0x80021d9c` | `0x80022088` | 748 | `system_user_exec_log_slot_tuples` | UNCONVERTED |
| `0x800225c4` | `0x80022868` | 676 | `account_tuple_sequences_consistent` | UNCONVERTED |
| `0x80022868` | `0x80022870` | 8 | `bal_all_accounts_tuple_sequences_consistent` | UNCONVERTED |
| `0x80022870` | `0x800229e0` | 368 | `bal_all_accounts_tuple_sequences_consistent_skip_list` | UNCONVERTED |
| `0x800229e0` | `0x80022b9c` | 444 | `bal_storage_reads_in_exec_log` | UNCONVERTED |
| `0x80022e0c` | `0x80022f04` | 248 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80023104` | `0x8002332c` | 552 | `bal_all_accounts_nonstorage_consistent` | UNCONVERTED |
| `0x80023968` | `0x80023a68` | 256 | `bti_scan_tuples` | UNCONVERTED |
| `0x80023b28` | `0x80023cf0` | 456 | `bal_txs_independent` | UNCONVERTED |
| `0x80023cf0` | `0x80023f20` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80023f20` | `0x80023f5c` | 60 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80023f5c` | `0x80024188` | 556 | `tx_intrinsic_state_gas` | UNCONVERTED |
| `0x8002446c` | `0x80024684` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80024684` | `0x80024878` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80024c0c` | `0x80025290` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80025290` | `0x80025610` | 896 | `simple_transfer_recipient_bal_verify` | UNCONVERTED |
| `0x80025610` | `0x800259ac` | 924 | `simple_transfer_fee_recipient_bal_verify` | UNCONVERTED |
| `0x80025d4c` | `0x800260c4` | 888 | `eip8037_state_used_before_tx` | UNCONVERTED |
| `0x800260c4` | `0x80026170` | 172 | `eip8037_prior_state_used_exact` | UNCONVERTED |
| `0x80026170` | `0x80026ab0` | 2368 | `eip8037_tx_gas_gate` | UNCONVERTED |
| `0x80026b18` | `0x80026c50` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80026c50` | `0x80026cb4` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x80026cb4` | `0x800271d0` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80027230` | `0x800272ec` | 188 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80027658` | `0x800277b0` | 344 | `eip7702_authorization_extract_signature` | UNCONVERTED |
| `0x80027968` | `0x80027af8` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x80027af8` | `0x800284ec` | 2548 | `tx_eip7702_existing_authority_refund` | UNCONVERTED |
| `0x800284ec` | `0x80028998` | 1196 | `eip7702_auth_nonstorage_effects` | UNCONVERTED |
| `0x80028d0c` | `0x80028fa8` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80028fa8` | `0x80028fe0` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x80029998` | `0x80029b2c` | 404 | `tx_legacy_extract_signature` | UNCONVERTED |
| `0x80029b2c` | `0x80029ce8` | 444 | `tx_eip2930_extract_signature` | UNCONVERTED |
| `0x80029ce8` | `0x80029eb8` | 464 | `tx_eip1559_extract_signature` | UNCONVERTED |
| `0x80029eb8` | `0x8002a0b0` | 504 | `tx_eip4844_extract_signature` | UNCONVERTED |
| `0x8002a0b0` | `0x8002a294` | 484 | `tx_eip7702_extract_signature` | UNCONVERTED |
| `0x8002ad0c` | `0x8002b9e4` | 3288 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002b9e4` | `0x8002bb6c` | 392 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002bb6c` | `0x8002bbe0` | 116 | `.preload_expand_loop` | UNCONVERTED |
| `0x8002bbe0` | `0x8002bc14` | 52 | `.preload_expand_done` | UNCONVERTED |
| `0x8002bc14` | `0x8002bc24` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002bc24` | `0x8002bc58` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002bc58` | `0x8002bc70` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002bc70` | `0x8002bc80` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002bc80` | `0x8002bcb4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002bcb4` | `0x8002bcbc` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002bcbc` | `0x8002bd08` | 76 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002bd08` | `0x8002bd38` | 48 | `.retag_preload_loop` | UNCONVERTED |
| `0x8002bd38` | `0x8002bd74` | 60 | `.retag_preload_done` | UNCONVERTED |
| `0x8002bd74` | `0x8002bd80` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002bd80` | `0x8002bda8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002bda8` | `0x8002bde0` | 56 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002bde0` | `0x8002bdec` | 12 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002bdec` | `0x8002be04` | 24 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002be04` | `0x8002be0c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002be0c` | `0x8002be18` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002be18` | `0x8002be30` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002be30` | `0x8002be48` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002be48` | `0x8002be5c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002be5c` | `0x8002be7c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002be7c` | `0x8002be90` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002be90` | `0x8002bebc` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002bebc` | `0x8002bf04` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002bf04` | `0x8002bf2c` | 40 | `.runtime_tx_auth_state_charge_done` | UNCONVERTED |
| `0x8002bf2c` | `0x8002bf50` | 36 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002bf50` | `0x8002bf50` | 0 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002bf50` | `0x8002bf74` | 36 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002bf74` | `0x8002c174` | 512 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002c174` | `0x8002c180` | 12 | `.jdbm_len_ok` | UNCONVERTED |
| `0x8002c180` | `0x8002c1bc` | 60 | `.jdbm_scan` | UNCONVERTED |
| `0x8002c1bc` | `0x8002c1e8` | 44 | `.jdbm_not_jumpdest` | UNCONVERTED |
| `0x8002c1e8` | `0x8002c1f4` | 12 | `.jdbm_push` | UNCONVERTED |
| `0x8002c1f4` | `0x8002c214` | 32 | `.jdbm_dupn_swapn` | UNCONVERTED |
| `0x8002c214` | `0x8002c230` | 28 | `.jdbm_exchange` | UNCONVERTED |
| `0x8002c230` | `0x8002c238` | 8 | `.jdbm_skip_eip8024_imm` | UNCONVERTED |
| `0x8002c238` | `0x8002c240` | 8 | `.jdbm_plain` | UNCONVERTED |
| `0x8002c240` | `0x8002c274` | 52 | `.jdbm_done` | UNCONVERTED |
| `0x8002c274` | `0x8002c370` | 252 | `.dispatch_loop` | UNCONVERTED |
| `0x8002c370` | `0x8002c4c4` | 340 | `balance_at_header_state_root` | UNCONVERTED |
| `0x8002d350` | `0x8002d378` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x8002d378` | `0x8002d498` | 288 | `create_record_code_effect` | UNCONVERTED |
| `0x8002d4f8` | `0x8002d614` | 284 | `create_creator_nonce_use` | UNCONVERTED |
| `0x8002d614` | `0x8002d664` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x8002d664` | `0x8002d6b4` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x8002d6b4` | `0x8002d6e4` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x8002d6e4` | `0x8002d728` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x8002d728` | `0x8002d76c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x8002d76c` | `0x8002d81c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8002d81c` | `0x8002d978` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x8002d978` | `0x8002dc74` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8002dc74` | `0x8002de50` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8002de50` | `0x8002defc` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x8002defc` | `0x8002e074` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x8002e074` | `0x8002e23c` | 456 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x8002e23c` | `0x8002e398` | 348 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x8002e410` | `0x8002e4ec` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8002e4ec` | `0x8002e63c` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x8002e63c` | `0x8002e818` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x8002e9c8` | `0x8002ebac` | 484 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8002ebac` | `0x8002ec00` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x8002ec00` | `0x8002ec48` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8002ec48` | `0x8002ed1c` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x8002ed1c` | `0x8002ee40` | 292 | `dispatcher_seed_pending_upfront_balance` | UNCONVERTED |
| `0x8002f4c0` | `0x8002f59c` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x8002f59c` | `0x8002f70c` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x8002f73c` | `0x8002f7b8` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x8002f7b8` | `0x8002f8a4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x8002ff08` | `0x8002ff78` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x8002ff78` | `0x8002ffd8` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x8003034c` | `0x800304dc` | 400 | `bnq_mul` | UNCONVERTED |
| `0x800304dc` | `0x80030530` | 84 | `bnq_add` | UNCONVERTED |
| `0x80030530` | `0x80030584` | 84 | `bnq_sub` | UNCONVERTED |
| `0x8003074c` | `0x800309b8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800309b8` | `0x80030cf8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80030cf8` | `0x80030fa8` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80030fa8` | `0x800312dc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800312dc` | `0x80031664` | 904 | `bng2_add` | UNCONVERTED |
| `0x80031664` | `0x80031784` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x800317a4` | `0x80031bd4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80031bd4` | `0x80032018` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003206c` | `0x80032218` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80032338` | `0x80032500` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x8003268c` | `0x80032850` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80032fe0` | `0x800332b8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003368c` | `0x8003379c` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x8003379c` | `0x800338f0` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x800338f0` | `0x80033a28` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80033ba4` | `0x80033c34` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80033c34` | `0x80033d04` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80033d04` | `0x80033edc` | 472 | `blq_mul` | UNCONVERTED |
| `0x80033edc` | `0x80033f38` | 92 | `blq_add` | UNCONVERTED |
| `0x80033f38` | `0x80033f94` | 92 | `blq_sub` | UNCONVERTED |
| `0x80034184` | `0x800343f0` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x800343f0` | `0x80034710` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80034710` | `0x800349c0` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800349c0` | `0x80034b9c` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80034b9c` | `0x80034ee4` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80035030` | `0x80036894` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x80036894` | `0x80037ad0` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x80037b54` | `0x80037bac` | 88 | `call_frame_enter` | UNCONVERTED |
| `0x80037bac` | `0x80037cc8` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x80037cd8` | `0x80037d08` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x80037d08` | `0x800381c8` | 1216 | `call_frame_descend` | UNCONVERTED |
| `0x800381c8` | `0x800382b8` | 240 | `create_frame_descend` | UNCONVERTED |
| `0x800382b8` | `0x800383d8` | 288 | `record_nonstorage_effect` | UNCONVERTED |
| `0x80038468` | `0x80038750` | 744 | `nonstorage_effect_aggregate` | UNCONVERTED |
| `0x80038750` | `0x80038ac8` | 888 | `frame_return` | UNCONVERTED |
| `0x80038ac8` | `0x80038b08` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x80038b08` | `0x80038b50` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x80038b50` | `0x80038ba0` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x80038ba0` | `0x80038bf8` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x80038bf8` | `0x80038c58` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x80038c58` | `0x80038cc0` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x80038cc0` | `0x80038d30` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x80038d30` | `0x80038da8` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x80038da8` | `0x80038e28` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x80038e28` | `0x80038eb0` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x80038eb0` | `0x80038f40` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x80038f40` | `0x80038fd8` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x80038fd8` | `0x80039078` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x80039078` | `0x80039120` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x80039120` | `0x800391d0` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x800391d0` | `0x80039288` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x80039288` | `0x80039348` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x80039348` | `0x80039410` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x80039410` | `0x800394e0` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x800394e0` | `0x800395b8` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x800395b8` | `0x80039698` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x80039698` | `0x80039780` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x80039780` | `0x80039870` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x80039870` | `0x80039968` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x80039968` | `0x80039a68` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x80039a68` | `0x80039b70` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x80039b70` | `0x80039c80` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x80039c80` | `0x80039d98` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x80039d98` | `0x80039eb8` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x80039eb8` | `0x80039fe0` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x80039fe0` | `0x8003a110` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003a110` | `0x8003a248` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003a248` | `0x8003a388` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003a388` | `0x8003a400` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003a400` | `0x8003a478` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003a478` | `0x8003a4f0` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003a4f0` | `0x8003a568` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003a568` | `0x8003a5e0` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003a5e0` | `0x8003a658` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003a658` | `0x8003a6d0` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003a6d0` | `0x8003a748` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003a748` | `0x8003a7c0` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003a7c0` | `0x8003a838` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003a838` | `0x8003a8b0` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003a8b0` | `0x8003a928` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003a928` | `0x8003a9a0` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003a9a0` | `0x8003aa18` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003aa18` | `0x8003aa90` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003aa90` | `0x8003ab08` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003ab08` | `0x8003ab78` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003ab78` | `0x8003abe8` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003abe8` | `0x8003ac58` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003ac58` | `0x8003acc8` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003acc8` | `0x8003ad38` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003ad38` | `0x8003ada8` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003ada8` | `0x8003ae18` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003ae18` | `0x8003ae88` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003ae88` | `0x8003aef8` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003aef8` | `0x8003af68` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003af68` | `0x8003afd8` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003afd8` | `0x8003b048` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003b048` | `0x8003b0b8` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003b0b8` | `0x8003b128` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003b128` | `0x8003b198` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003b198` | `0x8003b208` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003b208` | `0x8003b220` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003b220` | `0x8003b234` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003b234` | `0x8003b2c0` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003b2c0` | `0x8003b2d8` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003b2d8` | `0x8003b2ec` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003b2ec` | `0x8003b374` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003b374` | `0x8003b38c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003b38c` | `0x8003b3a0` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003b3a0` | `0x8003b3c0` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003b3c0` | `0x8003b3c8` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003b3c8` | `0x8003b3d4` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003b3d4` | `0x8003b3d8` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003b3d8` | `0x8003b45c` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003b45c` | `0x8003b504` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003b504` | `0x8003b638` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003b638` | `0x8003b6e0` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003b6e0` | `0x8003b7d8` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003b7d8` | `0x8003b870` | 152 | `h_LT` | UNCONVERTED |
| `0x8003b870` | `0x8003b908` | 152 | `h_GT` | UNCONVERTED |
| `0x8003b908` | `0x8003b99c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8003b99c` | `0x8003ba30` | 148 | `h_SGT` | UNCONVERTED |
| `0x8003ba30` | `0x8003bab4` | 132 | `h_EQ` | UNCONVERTED |
| `0x8003bab4` | `0x8003bb14` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8003bb14` | `0x8003bb88` | 116 | `h_AND` | UNCONVERTED |
| `0x8003bb88` | `0x8003bbfc` | 116 | `h_OR` | UNCONVERTED |
| `0x8003bbfc` | `0x8003bc70` | 116 | `h_XOR` | UNCONVERTED |
| `0x8003bc70` | `0x8003bcd0` | 96 | `h_NOT` | UNCONVERTED |
| `0x8003bcd0` | `0x8003bdbc` | 236 | `h_BYTE` | UNCONVERTED |
| `0x8003bdbc` | `0x8003bf5c` | 416 | `h_SHL` | UNCONVERTED |
| `0x8003bf5c` | `0x8003c0fc` | 416 | `h_SHR` | UNCONVERTED |
| `0x8003c0fc` | `0x8003c2b0` | 436 | `h_SAR` | UNCONVERTED |
| `0x8003c2b0` | `0x8003c3b0` | 256 | `h_CLZ` | UNCONVERTED |
| `0x8003c3b0` | `0x8003c3e4` | 52 | `h_POP` | UNCONVERTED |
| `0x8003c3e4` | `0x8003c644` | 608 | `h_MLOAD` | UNCONVERTED |
| `0x8003c644` | `0x8003c848` | 516 | `h_MSTORE` | UNCONVERTED |
| `0x8003c848` | `0x8003c944` | 252 | `h_MSTORE8` | UNCONVERTED |
| `0x8003c944` | `0x8003c988` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8003c988` | `0x8003c9cc` | 68 | `h_GAS` | UNCONVERTED |
| `0x8003c9cc` | `0x8003ca1c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x8003ca1c` | `0x8003ca6c` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x8003ca6c` | `0x8003cabc` | 80 | `h_CALLER` | UNCONVERTED |
| `0x8003cabc` | `0x8003cb0c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8003cb0c` | `0x8003cb5c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x8003cb5c` | `0x8003cbac` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x8003cbac` | `0x8003cbfc` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x8003cbfc` | `0x8003cc4c` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x8003cc4c` | `0x8003cc9c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x8003cc9c` | `0x8003ccec` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8003ccec` | `0x8003cd3c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x8003cd3c` | `0x8003cd8c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x8003cd8c` | `0x8003cddc` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8003cddc` | `0x8003ce2c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x8003ce2c` | `0x8003ce7c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x8003ce7c` | `0x8003cf14` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x8003cf14` | `0x8003cfbc` | 168 | `h_BLOCKHASH` | UNCONVERTED |
| `0x8003cfbc` | `0x8003d000` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8003d000` | `0x8003d21c` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x8003d21c` | `0x8003d38c` | 368 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x8003d38c` | `0x8003d3d0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x8003d3d0` | `0x8003d510` | 320 | `h_CODECOPY` | UNCONVERTED |
| `0x8003d510` | `0x8003d518` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x8003d518` | `0x8003d5d8` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8003d5d8` | `0x8003d6cc` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x8003d6cc` | `0x8003d710` | 68 | `h_PC` | UNCONVERTED |
| `0x8003d710` | `0x8003d974` | 612 | `h_KECCAK256` | UNCONVERTED |
| `0x8003d974` | `0x8003dc48` | 724 | `h_LOG0` | UNCONVERTED |
| `0x8003dc48` | `0x8003df3c` | 756 | `h_LOG1` | UNCONVERTED |
| `0x8003df3c` | `0x8003e250` | 788 | `h_LOG2` | UNCONVERTED |
| `0x8003e250` | `0x8003e584` | 820 | `h_LOG3` | UNCONVERTED |
| `0x8003e584` | `0x8003e8d8` | 852 | `h_LOG4` | UNCONVERTED |
| `0x8003e8d8` | `0x8003eb80` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x8003eb80` | `0x8003ee28` | 680 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8003ee28` | `0x8003f2f0` | 1224 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8003f2f0` | `0x8003f7bc` | 1228 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x8003f7bc` | `0x8003f8ec` | 304 | `h_SLOAD` | UNCONVERTED |
| `0x8003f8ec` | `0x8003fd48` | 1116 | `h_SSTORE` | UNCONVERTED |
| `0x8003fd48` | `0x8003fe34` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x8003fe34` | `0x8003ff04` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x8003ff04` | `0x80040148` | 580 | `h_MCOPY` | UNCONVERTED |
| `0x80040148` | `0x800406e0` | 1432 | `h_RETURN` | UNCONVERTED |
| `0x800406e0` | `0x80040990` | 688 | `h_REVERT` | UNCONVERTED |
| `0x80040990` | `0x800409ac` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800409ac` | `0x8004186c` | 3776 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x8004186c` | `0x800418b8` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x800418b8` | `0x800419ec` | 308 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800419ec` | `0x80042404` | 2584 | `h_CREATE` | UNCONVERTED |
| `0x80042404` | `0x80046684` | 17024 | `h_CALL` | UNCONVERTED |
| `0x80046684` | `0x80049968` | 13028 | `h_CALLCODE` | UNCONVERTED |
| `0x80049968` | `0x8004c904` | 12188 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004c904` | `0x8004d35c` | 2648 | `h_CREATE2` | UNCONVERTED |
| `0x8004d35c` | `0x8005077c` | 13344 | `h_STATICCALL` | UNCONVERTED |
| `0x8005077c` | `0x80051034` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x80051034` | `0x80051928` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80051928` | `0x80051ec4` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80051ec4` | `0x80052570` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80052570` | `0x80052590` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80052590` | `0x80052c3c` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80052c3c` | `0x80052c5c` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80052c5c` | `0x8005358c` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x8005358c` | `0x800538d8` | 844 | `h_EXP` | UNCONVERTED |
| `0x800538d8` | `0x80053948` | 112 | `h_STOP` | UNCONVERTED |
| `0x80053948` | `0x8005394c` | 4 | `h_invalid` | UNCONVERTED |
| `0x8005394c` | `0x80053974` | 40 | `.exit_static_violation` | UNCONVERTED |
| `0x80053974` | `0x800539c8` | 84 | `.exit_invalid` | UNCONVERTED |
| `0x800539c8` | `0x800539f0` | 40 | `.exit_invalid_top` | UNCONVERTED |
| `0x800539f0` | `0x80053a44` | 84 | `.exit_invalid_op` | UNCONVERTED |
| `0x80053a44` | `0x80053a6c` | 40 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80053a6c` | `0x80053a90` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80053a90` | `0x80053ab8` | 40 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80053ab8` | `0x80053b0c` | 84 | `.exit_outofgas` | UNCONVERTED |
| `0x80053b0c` | `0x80053b34` | 40 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053b34` | `0x80053b88` | 84 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80053b88` | `0x80053bb0` | 40 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80053bb0` | `0x80053c04` | 84 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053c04` | `0x80053c2c` | 40 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053c2c` | `0x80053c2c` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053c2c` | `0x80053c48` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053c48` | `0x80053d58` | 272 | `derive_block_system_requests` | UNCONVERTED |
| `0x80053d90` | `0x80053e5c` | 204 | `stage_system_call` | UNCONVERTED |
| `0x80053e5c` | `0x80053ffc` | 416 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053ffc` | `0x8005428c` | 656 | `block_verdict_append_direct_deposit` | UNCONVERTED |
| `0x8005428c` | `0x8005438c` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x8005438c` | `0x800544bc` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800544bc` | `0x80054518` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054518` | `0x80054538` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80054538` | `0x80054674` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054674` | `0x80054710` | 156 | `assemble_execution_requests` | UNCONVERTED |
| `0x800547a0` | `0x80054a88` | 744 | `stage_predeploy_storage_preload` | UNCONVERTED |
