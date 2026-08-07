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
not linked** (26 of 386 today — gas helpers etc. awaiting wiring); they are
excluded from `guestImageEntries` (the image `CodeReq` must reflect the
emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x8005510c), 348428 bytes (`RegionMap.textSizeBytes = 0x5510c`)

- symbols in `.text`: 912 (340 converted, 572 unconverted)
- covered by converted `_prog`s: 84272 bytes (24.19%)
- NOT covered: 264156 bytes (75.81%), 573 ranges

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
| `0x80000000` | `0x800016ac` | 5804 | `_start` | UNCONVERTED |
| `0x80001eac` | `0x80001edc` | 48 | `sg_load_u32le` | UNCONVERTED |
| `0x80001edc` | `0x80001efc` | 32 | `sg_memcpy` | UNCONVERTED |
| `0x80001efc` | `0x8000212c` | 560 | `ssz_htr_withdrawals` | UNCONVERTED |
| `0x8000212c` | `0x80002190` | 100 | `sg_htr_bv48` | UNCONVERTED |
| `0x80002190` | `0x800021e8` | 88 | `sg_htr_bv96` | UNCONVERTED |
| `0x800021e8` | `0x800022c8` | 224 | `sg_htr_deposit` | UNCONVERTED |
| `0x800022c8` | `0x8000237c` | 180 | `sg_htr_wr` | UNCONVERTED |
| `0x8000237c` | `0x80002414` | 152 | `sg_htr_cr` | UNCONVERTED |
| `0x80002414` | `0x800024c4` | 176 | `sg_htr_bd` | UNCONVERTED |
| `0x800024c4` | `0x80002548` | 132 | `sg_htr_be` | UNCONVERTED |
| `0x80002548` | `0x80002648` | 256 | `sg_htr_clist` | UNCONVERTED |
| `0x80002648` | `0x800027c0` | 376 | `ssz_htr_execution_requests` | UNCONVERTED |
| `0x80003878` | `0x80003ae4` | 620 | `witness_lookup_by_hash` | UNCONVERTED |
| `0x80003ae4` | `0x80003b00` | 28 | `widx_record_ptr` | UNCONVERTED |
| `0x80003b00` | `0x80003b40` | 64 | `widx_cmp32` | UNCONVERTED |
| `0x80003b40` | `0x80003b70` | 48 | `widx_swap_records` | UNCONVERTED |
| `0x80003b70` | `0x80003c6c` | 252 | `widx_sift_down` | UNCONVERTED |
| `0x80003c6c` | `0x80003ee4` | 632 | `witness_index_build` | UNCONVERTED |
| `0x80003ee4` | `0x80003fac` | 200 | `witness_lookup_by_hash_indexed` | UNCONVERTED |
| `0x80003fac` | `0x80004218` | 620 | `witness_codes_lookup_by_hash` | UNCONVERTED |
| `0x80004218` | `0x80004234` | 28 | `wcidx_record_ptr` | UNCONVERTED |
| `0x80004234` | `0x80004274` | 64 | `wcidx_cmp32` | UNCONVERTED |
| `0x80004274` | `0x800042a4` | 48 | `wcidx_swap_records` | UNCONVERTED |
| `0x800042a4` | `0x800043a0` | 252 | `wcidx_sift_down` | UNCONVERTED |
| `0x800043a0` | `0x80004618` | 632 | `witness_codes_index_build` | UNCONVERTED |
| `0x80004618` | `0x800046e0` | 200 | `witness_codes_lookup_by_hash_indexed` | UNCONVERTED |
| `0x80004d44` | `0x80004dd0` | 140 | `rlp_item_size` | UNCONVERTED |
| `0x80004dd0` | `0x80004ea4` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80004ea4` | `0x80004f78` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004f78` | `0x80005114` | 412 | `rlp_walk_next` | UNCONVERTED |
| `0x80005114` | `0x8000516c` | 88 | `rlp_content_to_u64` | UNCONVERTED |
| `0x8000516c` | `0x800051d4` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800051d4` | `0x800053c8` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009658` | `0x8000981c` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x8000981c` | `0x80009888` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x80009f48` | `0x8000a144` | 508 | `mpt_indexed_stream_leaf_hash` | UNCONVERTED |
| `0x8000a144` | `0x8000a344` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a344` | `0x8000a484` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a484` | `0x8000a740` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a740` | `0x8000a830` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a830` | `0x8000a9a0` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000b8d4` | `0x8000be64` | 1424 | `block_header_ssz_to_rlp` | UNCONVERTED |
| `0x8000c1e0` | `0x8000c3fc` | 540 | `execution_requests_hash` | UNCONVERTED |
| `0x8000c3fc` | `0x8000c458` | 92 | `erh_hash_one` | UNCONVERTED |
| `0x8000de8c` | `0x8000f1a0` | 4884 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x800100b8` | `0x80010418` | 864 | `append_modeled_system_storage_tuple_rows` | UNCONVERTED |
| `0x80010418` | `0x800104d0` | 184 | `record_modeled_eip4788_storage_reads` | UNCONVERTED |
| `0x800104d0` | `0x800106b0` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x800106b0` | `0x80010794` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x80010794` | `0x80010870` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x80010870` | `0x80010904` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010904` | `0x800109c0` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x800109c0` | `0x80010a70` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x80010a70` | `0x80010b54` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010b54` | `0x80010b90` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x80010b90` | `0x80010cc0` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x80010cc0` | `0x80010de4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010de4` | `0x80010e94` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010e94` | `0x80011010` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80011010` | `0x800110e8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800110e8` | `0x80011278` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80011278` | `0x80011414` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80011414` | `0x800114c4` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800114c4` | `0x8001152c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8001152c` | `0x800115c8` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800115c8` | `0x80011bfc` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011bfc` | `0x80011ee4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011ee4` | `0x8001223c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001223c` | `0x80012718` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80012718` | `0x800129bc` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800129bc` | `0x80012ad8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80012ad8` | `0x80012d90` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80012d90` | `0x80012fb0` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012fb0` | `0x80013348` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80013348` | `0x8001345c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001345c` | `0x8001347c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001347c` | `0x80013704` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80013704` | `0x800137e8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800137e8` | `0x80013968` | 384 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80013968` | `0x80014180` | 2072 | `execution_map_state_changes` | UNCONVERTED |
| `0x80014180` | `0x80014e38` | 3256 | `block_state_root` | UNCONVERTED |
| `0x80014e38` | `0x80015008` | 464 | `chain_config_valid` | UNCONVERTED |
| `0x80015008` | `0x80015174` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80015174` | `0x80015188` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80015188` | `0x80015194` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80015194` | `0x800151e4` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800151e4` | `0x80015204` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80015204` | `0x80015268` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80015268` | `0x80015510` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80015510` | `0x80015764` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80015764` | `0x80015918` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015918` | `0x80015d24` | 1036 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80016514` | `0x8001670c` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80016a2c` | `0x80016c58` | 556 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016d54` | `0x80017048` | 756 | `simple_transfer_intrinsic_gas` | UNCONVERTED |
| `0x80017048` | `0x80019b50` | 11016 | `block_verdict` | UNCONVERTED |
| `0x80019b50` | `0x8001a914` | 3524 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x8001a914` | `0x8001ab30` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x8001b604` | `0x8001b85c` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001b85c` | `0x8001bad4` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001bad4` | `0x8001bd68` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001c078` | `0x8001c214` | 412 | `bal_gas_valid_from_builder` | UNCONVERTED |
| `0x8001c428` | `0x8001c6c4` | 668 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ca8c` | `0x8001cc00` | 372 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001cc00` | `0x8001cda0` | 416 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001cda0` | `0x8001d7d4` | 2612 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001dadc` | `0x8001db24` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001dc58` | `0x8001e020` | 968 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001e020` | `0x8001e0b0` | 144 | `stage_runtime_payload_witness_context` | UNCONVERTED |
| `0x8001e0b0` | `0x8001e298` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001e298` | `0x8001e2f4` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001e2f4` | `0x8001e3c0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001e3c0` | `0x8001e494` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001e494` | `0x8001f394` | 3840 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001fc68` | `0x8001fd7c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001fd7c` | `0x80020084` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8002081c` | `0x80020970` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x80020d38` | `0x80020d78` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020d78` | `0x80020fd8` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x80020fd8` | `0x80021120` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80021120` | `0x80021150` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80021150` | `0x800212dc` | 396 | `storage_read_record` | UNCONVERTED |
| `0x800212dc` | `0x80021450` | 372 | `storage_read_record_block` | UNCONVERTED |
| `0x80021450` | `0x8002168c` | 572 | `storage_write_record` | UNCONVERTED |
| `0x8002168c` | `0x80021814` | 392 | `destroy_storage` | UNCONVERTED |
| `0x80021814` | `0x800219b0` | 412 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x800219b0` | `0x80021a6c` | 188 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x80021a6c` | `0x80021a94` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x80021a94` | `0x80021b8c` | 248 | `storage_writes_undo_push` | UNCONVERTED |
| `0x80021b8c` | `0x80021ccc` | 320 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80021ccc` | `0x80021f0c` | 576 | `account_write_record` | UNCONVERTED |
| `0x80021f0c` | `0x8002204c` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x8002204c` | `0x80022114` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x80022114` | `0x800221c4` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x800221c4` | `0x80022274` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80022274` | `0x800223e4` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x800223e4` | `0x800224c8` | 228 | `account_writes_auth_block` | UNCONVERTED |
| `0x800224c8` | `0x8002256c` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x8002256c` | `0x800226e8` | 380 | `account_writes_lookup_current` | UNCONVERTED |
| `0x800226e8` | `0x800229bc` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x800229bc` | `0x80022ad8` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80022ad8` | `0x80022c9c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80022c9c` | `0x80022f20` | 644 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022f20` | `0x80022f70` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x80022f70` | `0x80023064` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x80023064` | `0x80023568` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x80023568` | `0x800235f4` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x800235f4` | `0x80023714` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023714` | `0x80023818` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x80023818` | `0x800239d4` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x800239d4` | `0x80023e30` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x80023e30` | `0x800240d8` | 680 | `bal_map_final_value_matches` | UNCONVERTED |
| `0x800240d8` | `0x800241c8` | 240 | `bal_map_builder_consistent` | UNCONVERTED |
| `0x80024414` | `0x80024430` | 28 | `keccak_init` | UNCONVERTED |
| `0x80024430` | `0x800244a4` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800244a4` | `0x800244f4` | 80 | `keccak_final` | UNCONVERTED |
| `0x800244f4` | `0x80024520` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80024520` | `0x80024600` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80024600` | `0x80024680` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80024680` | `0x800246b0` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800246b0` | `0x800247f0` | 320 | `bal_rlp_emit_bytes` | UNCONVERTED |
| `0x800247f0` | `0x800248b4` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800248b4` | `0x80024908` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80024908` | `0x80024938` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80024938` | `0x80024978` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80024978` | `0x800249b0` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800249b0` | `0x800249f0` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800249f0` | `0x80024aac` | 188 | `bal_serializer_slot_written` | UNCONVERTED |
| `0x80024aac` | `0x80024b50` | 164 | `bal_serializer_slot_seen_before` | UNCONVERTED |
| `0x80024b50` | `0x80024b68` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b68` | `0x80024c38` | 208 | `bal_serializer_measure_reads` | UNCONVERTED |
| `0x80024c38` | `0x80024c68` | 48 | `bal_serializer_slot_to_le` | UNCONVERTED |
| `0x80024c68` | `0x80024c98` | 48 | `bal_serializer_balance_to_le` | UNCONVERTED |
| `0x80024c98` | `0x80024da4` | 268 | `bal_serializer_measure_slot` | UNCONVERTED |
| `0x80024da4` | `0x80024e84` | 224 | `bal_serializer_measure_storage` | UNCONVERTED |
| `0x80024e84` | `0x80024f60` | 220 | `bal_serializer_measure_balance` | UNCONVERTED |
| `0x80024f60` | `0x80025048` | 232 | `bal_serializer_measure_nonce` | UNCONVERTED |
| `0x80025048` | `0x80025138` | 240 | `bal_serializer_measure_code` | UNCONVERTED |
| `0x80025138` | `0x8002521c` | 228 | `bal_serializer_measure_account` | UNCONVERTED |
| `0x8002521c` | `0x800253fc` | 480 | `bal_serializer_emit_storage` | UNCONVERTED |
| `0x800253fc` | `0x800254c4` | 200 | `bal_serializer_emit_reads` | UNCONVERTED |
| `0x800254c4` | `0x80025608` | 324 | `bal_serializer_emit_balance` | UNCONVERTED |
| `0x80025608` | `0x80025780` | 376 | `bal_serializer_emit_nonce` | UNCONVERTED |
| `0x80025780` | `0x800258b4` | 308 | `bal_serializer_emit_code` | UNCONVERTED |
| `0x800258b4` | `0x800259e0` | 300 | `bal_serializer_emit_account` | UNCONVERTED |
| `0x800259e0` | `0x80025a70` | 144 | `bal_serializer_measure_outer` | UNCONVERTED |
| `0x80025a70` | `0x80025b18` | 168 | `bal_serializer_emit_outer` | UNCONVERTED |
| `0x80025b18` | `0x80025ce0` | 456 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80025ce0` | `0x80025d78` | 152 | `bal_serializer_verify` | UNCONVERTED |
| `0x80025d78` | `0x80025e84` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025e84` | `0x80025ee4` | 96 | `bal_builder_incorporate_touched_accounts` | UNCONVERTED |
| `0x80025ee4` | `0x800260ac` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800260ac` | `0x8002638c` | 736 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x8002638c` | `0x80026474` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80026474` | `0x80026550` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80026550` | `0x80026628` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80026628` | `0x80026748` | 288 | `account_read_record` | UNCONVERTED |
| `0x80026748` | `0x8002679c` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x8002679c` | `0x800268f8` | 348 | `code_read_record` | UNCONVERTED |
| `0x800268f8` | `0x800269a4` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x800269a4` | `0x80026ac8` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80026ac8` | `0x80026b9c` | 212 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026b9c` | `0x80026bc4` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x80026bc4` | `0x80026cec` | 296 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80026e40` | `0x800270dc` | 668 | `bal_all_accounts_nonstorage_consistent` | UNCONVERTED |
| `0x80027718` | `0x80027948` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80027948` | `0x80027958` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80027b3c` | `0x80027d54` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80027d54` | `0x80027f48` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800282dc` | `0x80028960` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800296e0` | `0x80029818` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80029818` | `0x8002987c` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x8002987c` | `0x80029d98` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80029df8` | `0x80029e98` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x8002a240` | `0x8002a398` | 344 | `eip7702_authorization_extract_signature` | UNCONVERTED |
| `0x8002a550` | `0x8002a6e0` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x8002a6e0` | `0x8002a9fc` | 796 | `eip7702_authority_asof` | UNCONVERTED |
| `0x8002a9fc` | `0x8002b1c0` | 1988 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002b1c0` | `0x8002b4e0` | 800 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x8002b4e0` | `0x8002b5d0` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x8002b83c` | `0x8002bad8` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002bad8` | `0x8002bb10` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002bed8` | `0x8002bfc4` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002c114` | `0x8002c2a8` | 404 | `tx_legacy_extract_signature` | UNCONVERTED |
| `0x8002c2a8` | `0x8002c464` | 444 | `tx_eip2930_extract_signature` | UNCONVERTED |
| `0x8002c464` | `0x8002c634` | 464 | `tx_eip1559_extract_signature` | UNCONVERTED |
| `0x8002c634` | `0x8002c82c` | 504 | `tx_eip4844_extract_signature` | UNCONVERTED |
| `0x8002c82c` | `0x8002ca10` | 484 | `tx_eip7702_extract_signature` | UNCONVERTED |
| `0x8002d708` | `0x8002dbf8` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002dbf8` | `0x8002e6a8` | 2736 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002e6a8` | `0x8002ec78` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002ec78` | `0x80030638` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x80030638` | `0x8003065c` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8003065c` | `0x80030678` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x80030678` | `0x80030940` | 712 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x80030940` | `0x80030950` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x80030950` | `0x80030984` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x80030984` | `0x8003099c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8003099c` | `0x800309ac` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x800309ac` | `0x800309e0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x800309e0` | `0x800309e8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x800309e8` | `0x80030a94` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x80030a94` | `0x80030aa0` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x80030aa0` | `0x80030ac8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x80030ac8` | `0x80030b08` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x80030b08` | `0x80030b38` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x80030b38` | `0x80030b38` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x80030b38` | `0x80030b50` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x80030b50` | `0x80030b58` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x80030b58` | `0x80030b64` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x80030b64` | `0x80030b7c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x80030b7c` | `0x80030b94` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030b94` | `0x80030ba8` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030ba8` | `0x80030bc8` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030bc8` | `0x80030bdc` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030bdc` | `0x80030c08` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x80030c08` | `0x80030c50` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x80030c50` | `0x80030d24` | 212 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x80030d24` | `0x80030dd4` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030dd4` | `0x80030df4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030df4` | `0x80030e68` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030e68` | `0x80030e78` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030e78` | `0x80030e84` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x80030e84` | `0x80030f68` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030f68` | `0x80030f90` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x80030f90` | `0x80030fa4` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030fa4` | `0x80030fa4` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030fa4` | `0x80030fa4` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030fa4` | `0x80030fc4` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030fc4` | `0x80030ff4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030ff4` | `0x80031018` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x80031018` | `0x80031040` | 40 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x80031040` | `0x800310cc` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x800310cc` | `0x800310dc` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x800310dc` | `0x800310ec` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800310ec` | `0x8003121c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8003121c` | `0x800313b8` | 412 | `.dispatch_loop` | UNCONVERTED |
| `0x800313b8` | `0x80031418` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031418` | `0x80031570` | 344 | `balance_at_header_state_root` | UNCONVERTED |
| `0x800321d0` | `0x800321f8` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800321f8` | `0x80032408` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80032468` | `0x80032514` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80032514` | `0x80032598` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80032598` | `0x80032618` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80032618` | `0x800326d0` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x800326d0` | `0x80032744` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80032744` | `0x80032908` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80032908` | `0x80032978` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80032978` | `0x800329f0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x800329f0` | `0x80032ba0` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80032ba0` | `0x80032c1c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032c1c` | `0x80032c6c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80032c6c` | `0x80032cbc` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80032cbc` | `0x80032cec` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032cec` | `0x80032d30` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032d30` | `0x80032d74` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80032d74` | `0x80032e24` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032e24` | `0x80032f80` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80032f80` | `0x8003327c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003327c` | `0x80033458` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80033458` | `0x80033504` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80033504` | `0x8003367c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x8003367c` | `0x80033848` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80033848` | `0x8003397c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80033a3c` | `0x80033b18` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80033b18` | `0x80033c68` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80033c68` | `0x80033e44` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033ff4` | `0x800341d8` | 484 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800341d8` | `0x8003422c` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x8003422c` | `0x80034274` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80034274` | `0x80034348` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80034348` | `0x80034428` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80034428` | `0x800345e0` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x800345e0` | `0x800346fc` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x80034d7c` | `0x80034e58` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x80034e58` | `0x80034fc8` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80034ff8` | `0x80035074` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80035074` | `0x80035160` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800357c4` | `0x80035834` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80035834` | `0x80035894` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80035ae0` | `0x80035c70` | 400 | `bnq_mul` | UNCONVERTED |
| `0x80035c70` | `0x80035cc4` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035e8c` | `0x800360f8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800360f8` | `0x80036438` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80036438` | `0x800366e8` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800366e8` | `0x80036a1c` | 820 | `bng2_double` | UNCONVERTED |
| `0x80036a1c` | `0x80036da4` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036da4` | `0x80036ec4` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036ee4` | `0x80037314` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80037314` | `0x80037758` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x800377ac` | `0x80037958` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037a78` | `0x80037c40` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80037dcc` | `0x80037f90` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80038720` | `0x800389f8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038dcc` | `0x80038edc` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80038edc` | `0x80039030` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80039030` | `0x80039168` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x800392e4` | `0x80039374` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80039374` | `0x80039444` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80039444` | `0x8003961c` | 472 | `blq_mul` | UNCONVERTED |
| `0x8003961c` | `0x80039678` | 92 | `blq_sub` | UNCONVERTED |
| `0x80039868` | `0x80039ad4` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039ad4` | `0x80039df4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039df4` | `0x8003a0a4` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003a0a4` | `0x8003a280` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x8003a280` | `0x8003a5c8` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x8003a714` | `0x8003bf78` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003bf78` | `0x8003d1b4` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003d234` | `0x8003d2d8` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003d2d8` | `0x8003d3f4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003d404` | `0x8003d434` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003d434` | `0x8003d9d0` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003d9d0` | `0x8003dce0` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003dce0` | `0x8003dce8` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003dce8` | `0x8003dcec` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003dcec` | `0x8003ded0` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003df60` | `0x8003dfc8` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003dfc8` | `0x8003e43c` | 1140 | `nonstorage_effect_aggregate` | UNCONVERTED |
| `0x8003e43c` | `0x8003e684` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003e684` | `0x8003ece8` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ece8` | `0x8003ee04` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003ee04` | `0x8003f01c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003f01c` | `0x8003f05c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003f05c` | `0x8003f0a4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003f0a4` | `0x8003f0f4` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003f0f4` | `0x8003f14c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003f14c` | `0x8003f1ac` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003f1ac` | `0x8003f214` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003f214` | `0x8003f284` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003f284` | `0x8003f2fc` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003f2fc` | `0x8003f37c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003f37c` | `0x8003f404` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003f404` | `0x8003f494` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003f494` | `0x8003f52c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003f52c` | `0x8003f5cc` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003f5cc` | `0x8003f674` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003f674` | `0x8003f724` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003f724` | `0x8003f7dc` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003f7dc` | `0x8003f89c` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003f89c` | `0x8003f964` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003f964` | `0x8003fa34` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003fa34` | `0x8003fb0c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003fb0c` | `0x8003fbec` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003fbec` | `0x8003fcd4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003fcd4` | `0x8003fdc4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003fdc4` | `0x8003febc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003febc` | `0x8003ffbc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ffbc` | `0x800400c4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x800400c4` | `0x800401d4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x800401d4` | `0x800402ec` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x800402ec` | `0x8004040c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8004040c` | `0x80040534` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x80040534` | `0x80040664` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x80040664` | `0x8004079c` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8004079c` | `0x800408dc` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x800408dc` | `0x80040954` | 120 | `h_DUP1` | UNCONVERTED |
| `0x80040954` | `0x800409cc` | 120 | `h_DUP2` | UNCONVERTED |
| `0x800409cc` | `0x80040a44` | 120 | `h_DUP3` | UNCONVERTED |
| `0x80040a44` | `0x80040abc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x80040abc` | `0x80040b34` | 120 | `h_DUP5` | UNCONVERTED |
| `0x80040b34` | `0x80040bac` | 120 | `h_DUP6` | UNCONVERTED |
| `0x80040bac` | `0x80040c24` | 120 | `h_DUP7` | UNCONVERTED |
| `0x80040c24` | `0x80040c9c` | 120 | `h_DUP8` | UNCONVERTED |
| `0x80040c9c` | `0x80040d14` | 120 | `h_DUP9` | UNCONVERTED |
| `0x80040d14` | `0x80040d8c` | 120 | `h_DUP10` | UNCONVERTED |
| `0x80040d8c` | `0x80040e04` | 120 | `h_DUP11` | UNCONVERTED |
| `0x80040e04` | `0x80040e7c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x80040e7c` | `0x80040ef4` | 120 | `h_DUP13` | UNCONVERTED |
| `0x80040ef4` | `0x80040f6c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040f6c` | `0x80040fe4` | 120 | `h_DUP15` | UNCONVERTED |
| `0x80040fe4` | `0x8004105c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8004105c` | `0x800410cc` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800410cc` | `0x8004113c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8004113c` | `0x800411ac` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800411ac` | `0x8004121c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8004121c` | `0x8004128c` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8004128c` | `0x800412fc` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800412fc` | `0x8004136c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8004136c` | `0x800413dc` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800413dc` | `0x8004144c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8004144c` | `0x800414bc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800414bc` | `0x8004152c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004152c` | `0x8004159c` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8004159c` | `0x8004160c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004160c` | `0x8004167c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004167c` | `0x800416ec` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800416ec` | `0x8004175c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004175c` | `0x80041774` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80041774` | `0x80041788` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80041788` | `0x80041814` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80041814` | `0x8004182c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004182c` | `0x80041840` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80041840` | `0x800418c8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800418c8` | `0x800418e0` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800418e0` | `0x800418f4` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800418f4` | `0x80041914` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80041914` | `0x8004191c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004191c` | `0x80041928` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80041928` | `0x8004192c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004192c` | `0x800419b0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800419b0` | `0x80041a58` | 168 | `h_ADD` | UNCONVERTED |
| `0x80041a58` | `0x80041b8c` | 308 | `h_MUL` | UNCONVERTED |
| `0x80041b8c` | `0x80041c34` | 168 | `h_SUB` | UNCONVERTED |
| `0x80041c34` | `0x80041d2c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80041d2c` | `0x80041dc4` | 152 | `h_LT` | UNCONVERTED |
| `0x80041dc4` | `0x80041e5c` | 152 | `h_GT` | UNCONVERTED |
| `0x80041e5c` | `0x80041ef0` | 148 | `h_SLT` | UNCONVERTED |
| `0x80041ef0` | `0x80041f84` | 148 | `h_SGT` | UNCONVERTED |
| `0x80041f84` | `0x80042008` | 132 | `h_EQ` | UNCONVERTED |
| `0x80042008` | `0x80042068` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80042068` | `0x800420dc` | 116 | `h_AND` | UNCONVERTED |
| `0x800420dc` | `0x80042150` | 116 | `h_OR` | UNCONVERTED |
| `0x80042150` | `0x800421c4` | 116 | `h_XOR` | UNCONVERTED |
| `0x800421c4` | `0x80042224` | 96 | `h_NOT` | UNCONVERTED |
| `0x80042224` | `0x80042310` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80042310` | `0x800424b0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800424b0` | `0x80042650` | 416 | `h_SHR` | UNCONVERTED |
| `0x80042650` | `0x80042804` | 436 | `h_SAR` | UNCONVERTED |
| `0x80042804` | `0x80042904` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80042904` | `0x80042938` | 52 | `h_POP` | UNCONVERTED |
| `0x80042938` | `0x80042cb4` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80042cb4` | `0x80042fc4` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80042fc4` | `0x800430fc` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x800430fc` | `0x80043140` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80043140` | `0x80043184` | 68 | `h_GAS` | UNCONVERTED |
| `0x80043184` | `0x800431d4` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x800431d4` | `0x80043224` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80043224` | `0x80043274` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80043274` | `0x800432c4` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x800432c4` | `0x80043314` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80043314` | `0x80043364` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80043364` | `0x800433b4` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800433b4` | `0x80043404` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80043404` | `0x80043454` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80043454` | `0x800434a4` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800434a4` | `0x800434f4` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800434f4` | `0x80043544` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80043544` | `0x80043594` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80043594` | `0x800435e4` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800435e4` | `0x80043634` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80043634` | `0x800436cc` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800436cc` | `0x800437b8` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800437b8` | `0x800437fc` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800437fc` | `0x80043a18` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80043a18` | `0x80043c00` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80043c00` | `0x80043c44` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80043c44` | `0x80043e28` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80043e28` | `0x80043e30` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80043e30` | `0x80043ef0` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80043ef0` | `0x80043fe4` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80043fe4` | `0x80044028` | 68 | `h_PC` | UNCONVERTED |
| `0x80044028` | `0x800442b0` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800442b0` | `0x800445a0` | 752 | `h_LOG0` | UNCONVERTED |
| `0x800445a0` | `0x800448b0` | 784 | `h_LOG1` | UNCONVERTED |
| `0x800448b0` | `0x80044be0` | 816 | `h_LOG2` | UNCONVERTED |
| `0x80044be0` | `0x80044f30` | 848 | `h_LOG3` | UNCONVERTED |
| `0x80044f30` | `0x800452a0` | 880 | `h_LOG4` | UNCONVERTED |
| `0x800452a0` | `0x80045548` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80045548` | `0x80045850` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80045850` | `0x80045ebc` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80045ebc` | `0x8004647c` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x8004647c` | `0x800469e4` | 1384 | `h_SLOAD` | UNCONVERTED |
| `0x800469e4` | `0x8004725c` | 2168 | `h_SSTORE` | UNCONVERTED |
| `0x8004725c` | `0x80047348` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80047348` | `0x80047418` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80047418` | `0x800476b0` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x800476b0` | `0x80048038` | 2440 | `h_RETURN` | UNCONVERTED |
| `0x80048038` | `0x8004860c` | 1492 | `h_REVERT` | UNCONVERTED |
| `0x8004860c` | `0x80048628` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80048628` | `0x80049b4c` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80049b4c` | `0x80049b98` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80049b98` | `0x80049d54` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80049d54` | `0x8004ab0c` | 3512 | `h_CREATE` | UNCONVERTED |
| `0x8004ab0c` | `0x8004cd28` | 8732 | `h_CALL` | UNCONVERTED |
| `0x8004cd28` | `0x8004ddec` | 4292 | `h_CALLCODE` | UNCONVERTED |
| `0x8004ddec` | `0x8004ea44` | 3160 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004ea44` | `0x8004f83c` | 3576 | `h_CREATE2` | UNCONVERTED |
| `0x8004f83c` | `0x80050494` | 3160 | `h_STATICCALL` | UNCONVERTED |
| `0x80050494` | `0x80050d4c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x80050d4c` | `0x80051640` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80051640` | `0x80051bdc` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80051bdc` | `0x80052288` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80052288` | `0x800522a8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800522a8` | `0x80052954` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80052954` | `0x80052974` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80052974` | `0x800532a4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800532a4` | `0x800535f0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800535f0` | `0x80053760` | 368 | `h_STOP` | UNCONVERTED |
| `0x80053760` | `0x80053764` | 4 | `h_invalid` | UNCONVERTED |
| `0x80053764` | `0x800537ec` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800537ec` | `0x800539e0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800539e0` | `0x80053a10` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80053a10` | `0x80053a24` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80053a24` | `0x80053a34` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80053a34` | `0x80053a5c` | 40 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80053a5c` | `0x80053c50` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80053c50` | `0x80053c80` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80053c80` | `0x80053c94` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80053c94` | `0x80053ca4` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80053ca4` | `0x80053ccc` | 40 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80053ccc` | `0x80053cf0` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80053cf0` | `0x80053d18` | 40 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80053d18` | `0x80053f0c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80053f0c` | `0x80053f3c` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053f3c` | `0x80053f50` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053f50` | `0x80053f60` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053f60` | `0x80053f88` | 40 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80053f88` | `0x8005417c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005417c` | `0x800541ac` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800541ac` | `0x800541c0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800541c0` | `0x800541d0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800541d0` | `0x800541f8` | 40 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800541f8` | `0x800543ec` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800543ec` | `0x8005441c` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x8005441c` | `0x80054430` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80054430` | `0x80054440` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80054440` | `0x80054468` | 40 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80054468` | `0x80054468` | 0 | `.exit_label` | UNCONVERTED |
| `0x80054468` | `0x80054484` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800544bc` | `0x800544d8` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x800544d8` | `0x800544f4` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x800544f4` | `0x800545d8` | 228 | `stage_system_call` | UNCONVERTED |
| `0x800545d8` | `0x800547d4` | 508 | `stage_system_call_payload` | UNCONVERTED |
| `0x800547d4` | `0x800548b8` | 228 | `block_verdict_all_direct_deposit_txs` | UNCONVERTED |
| `0x800548b8` | `0x80054b48` | 656 | `block_verdict_append_direct_deposit` | UNCONVERTED |
| `0x80054b48` | `0x80054c48` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x80054c48` | `0x80054d78` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054d78` | `0x80054dd4` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054dd4` | `0x80054df4` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80054df4` | `0x80054f30` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054f30` | `0x80055070` | 320 | `assemble_execution_requests` | UNCONVERTED |
| `0x80055100` | `0x8005510c` | 12 | `requests_hash_verify` | TAIL |
