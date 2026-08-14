# Guest-image CodeReq coverage accounting (bead evm-asm-4ch8f.63)

What fraction of the linked `stateless_guest` `.text` the composed
`guestImageCodeReq` (`EvmAsm/Codegen/Proofs/GuestImage.lean`, entries table
`GuestImageEntries.lean`) actually covers, and the precise list of what it
does NOT — every uncovered range is work someone must do before the `.64`
end-to-end theorem can run over the FULL image. Child beads under `.63`
track the clusters (§2).

**GENERATED FILE — do not hand-edit.** This document is rendered from
`scripts/asm-fixtures/guest-image-coverage-template.md` (prose and
placeholder slots only — no figures) plus live numbers from the generator:

```
python3 scripts/guest_image_coverage.py --write-doc   # regenerate THIS FILE
python3 scripts/guest_image_coverage.py --check-doc   # drift check
```

The drift check is wired into CI as `scripts/check-guest-image-coverage.sh`
in the `reports` lane of `scripts/check-build-parallel.sh`, so a layout or
manifest change that moves the §1 numbers or the §3 table without a
`--write-doc` regeneration fails the build. Other generator modes
(unchanged):

```
python3 scripts/guest_image_coverage.py            # human summary + gaps
python3 scripts/guest_image_coverage.py --md       # §1 numbers + §3 table to stdout
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
not linked** (96 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053e98), 343704 bytes (`RegionMap.textSizeBytes = 0x53e98`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121728 bytes (35.42%)
- NOT covered: 221976 bytes (64.58%), 458 ranges

Everything covered is anchored BY NAME (`GuestAddrs.<entry>`), so layout
regens flow through `GuestAddrs.lean` without touching the entries table
(addresses) — only add/remove of functions or length changes regenerate it.
The kernel-checked extent fact `guestImageEntries_extentsOk`
(`GuestImage.lean`) is the whole-image disjointness certificate.

## 2. Gap clusters → child beads

> **Editorial section — NOT covered by the drift guard.** Cluster boundaries
> are hand-drawn and the byte counts are approximate binnings of §3; the
> guard pins §1's numbers and §3's table only. For current figures trust §3
> and the generator, not this table.

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

## 3. Full gap table (generated)

| start | end | bytes | symbol | kind |
|---|---|---|---|---|
| `0x80000000` | `0x80001948` | 6472 | `_start` | UNCONVERTED |
| `0x80002148` | `0x80002178` | 48 | `sg_load_u32le` | UNCONVERTED |
| `0x80002178` | `0x80002198` | 32 | `sg_memcpy` | UNCONVERTED |
| `0x80002198` | `0x800023c8` | 560 | `ssz_htr_withdrawals` | UNCONVERTED |
| `0x800023c8` | `0x8000242c` | 100 | `sg_htr_bv48` | UNCONVERTED |
| `0x8000242c` | `0x80002484` | 88 | `sg_htr_bv96` | UNCONVERTED |
| `0x80002484` | `0x80002564` | 224 | `sg_htr_deposit` | UNCONVERTED |
| `0x80002564` | `0x80002618` | 180 | `sg_htr_wr` | UNCONVERTED |
| `0x80002618` | `0x800026b0` | 152 | `sg_htr_cr` | UNCONVERTED |
| `0x800026b0` | `0x80002760` | 176 | `sg_htr_bd` | UNCONVERTED |
| `0x80002760` | `0x800027e4` | 132 | `sg_htr_be` | UNCONVERTED |
| `0x800027e4` | `0x800028e4` | 256 | `sg_htr_clist` | UNCONVERTED |
| `0x800028e4` | `0x80002a5c` | 376 | `ssz_htr_execution_requests` | UNCONVERTED |
| `0x8000506c` | `0x80005140` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80005140` | `0x80005214` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80005514` | `0x8000555c` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x8000555c` | `0x800055c4` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800055c4` | `0x8000561c` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x8000561c` | `0x80005684` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005684` | `0x80005878` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009b54` | `0x80009d18` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009d18` | `0x80009d84` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a640` | `0x8000a840` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a840` | `0x8000a980` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a980` | `0x8000ac3c` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000ac3c` | `0x8000ad2c` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ad2c` | `0x8000ae9c` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e1d0` | `0x8000f4ec` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f91c` | `0x8000fafc` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fafc` | `0x8000fbe0` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fbe0` | `0x8000fcbc` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fcbc` | `0x8000fd50` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fd50` | `0x8000fe0c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fe0c` | `0x8000febc` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000febc` | `0x8000ffa0` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000ffa0` | `0x8000ffdc` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000ffdc` | `0x8001010c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001010c` | `0x80010230` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010230` | `0x800102e0` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800102e0` | `0x8001045c` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8001045c` | `0x80010534` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010534` | `0x800106c4` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x800106c4` | `0x80010860` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010860` | `0x80010910` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010910` | `0x80010978` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010978` | `0x80010a14` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010a14` | `0x80011048` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011048` | `0x80011330` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011330` | `0x80011688` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011688` | `0x80011b64` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011b64` | `0x80011e08` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011e08` | `0x80011f24` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011f24` | `0x800121dc` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800121dc` | `0x800123fc` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800123fc` | `0x80012794` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012794` | `0x800128a8` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x800128a8` | `0x800128c8` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x800128c8` | `0x80012b50` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012b50` | `0x80012c34` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012c34` | `0x80012cdc` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012cdc` | `0x80013410` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013410` | `0x80013a48` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013d84` | `0x80013d98` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d98` | `0x80013da4` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013da4` | `0x80013df4` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013df4` | `0x80013e14` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013e14` | `0x80013e78` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013e78` | `0x80014120` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014120` | `0x80014374` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014374` | `0x80014528` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015128` | `0x80015320` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015640` | `0x80015870` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015c60` | `0x8001875c` | 11004 | `block_verdict` | UNCONVERTED |
| `0x8001875c` | `0x800194f0` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800194f0` | `0x8001970c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800199f4` | `0x80019a88` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a280` | `0x8001a4d8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a4d8` | `0x8001a750` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a750` | `0x8001a9e4` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001afe0` | `0x8001b2fc` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b6c4` | `0x8001b93c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b93c` | `0x8001bbe0` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bbe0` | `0x8001c6a4` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c9b8` | `0x8001ca00` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d090` | `0x8001d278` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d278` | `0x8001d2d4` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d2d4` | `0x8001d3a0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d3a0` | `0x8001d474` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d474` | `0x8001e3f4` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ecc8` | `0x8001eddc` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001eddc` | `0x8001f0e4` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fd98` | `0x8001fdd8` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020038` | `0x80020180` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020180` | `0x800201b0` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020700` | `0x80020890` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021a84` | `0x80021ba0` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021ba0` | `0x80021d64` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021d64` | `0x80021ff4` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800226c8` | `0x800227e8` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800234e8` | `0x80023504` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023504` | `0x80023578` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023578` | `0x800235c8` | 80 | `keccak_final` | UNCONVERTED |
| `0x800235c8` | `0x800235f4` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800235f4` | `0x800236d4` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800236d4` | `0x80023754` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023754` | `0x80023784` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800238c4` | `0x80023988` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023988` | `0x800239dc` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800239dc` | `0x80023a0c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023a0c` | `0x80023a4c` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023a4c` | `0x80023a84` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023a84` | `0x80023ac4` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023c24` | `0x80023c3c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024bfc` | `0x80024df8` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024e90` | `0x80024f9c` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025000` | `0x800251c8` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800251c8` | `0x800254b0` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800254b0` | `0x80025598` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025598` | `0x80025674` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025674` | `0x8002574c` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025b00` | `0x80025c24` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025c24` | `0x80025d1c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026544` | `0x80026554` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026738` | `0x80026950` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026950` | `0x80026b44` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026ed8` | `0x8002755c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028478` | `0x80028994` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800289f4` | `0x80028a94` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800296e0` | `0x80029ed4` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a568` | `0x8002a804` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a804` | `0x8002a83c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c498` | `0x8002c990` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c990` | `0x8002d5b4` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d5b4` | `0x8002db84` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002db84` | `0x8002f544` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f544` | `0x8002f568` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f568` | `0x8002f584` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f584` | `0x8002f848` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f848` | `0x8002f858` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f858` | `0x8002f88c` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f88c` | `0x8002f8a4` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f8a4` | `0x8002f8b4` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f8b4` | `0x8002f8e8` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f8e8` | `0x8002f8f0` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f8f0` | `0x8002f99c` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f99c` | `0x8002f9a8` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f9a8` | `0x8002f9d0` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f9d0` | `0x8002fa10` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002fa10` | `0x8002fa40` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002fa40` | `0x8002fa40` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002fa40` | `0x8002fa58` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fa58` | `0x8002fa60` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fa60` | `0x8002fa6c` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002fa6c` | `0x8002fa84` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fa84` | `0x8002fa9c` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fa9c` | `0x8002fab0` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002fab0` | `0x8002fad0` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002fad0` | `0x8002fae4` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002fae4` | `0x8002fb10` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fb10` | `0x8002fb58` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fb58` | `0x8002fc38` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fc38` | `0x8002fce8` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fce8` | `0x8002fd08` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fd08` | `0x8002fd7c` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fd7c` | `0x8002fd8c` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fd8c` | `0x8002fd98` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fd98` | `0x8002fe7c` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fe7c` | `0x8002fea4` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fea4` | `0x8002feb8` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002feb8` | `0x8002feb8` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002feb8` | `0x8002feb8` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002feb8` | `0x8002fed8` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fed8` | `0x8002ff08` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002ff08` | `0x8002ff2c` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002ff2c` | `0x8002ff4c` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002ff4c` | `0x8002ff50` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002ff50` | `0x8002ffdc` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002ffdc` | `0x8002ffec` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002ffec` | `0x8002fffc` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fffc` | `0x8003012c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8003012c` | `0x8003012c` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8003012c` | `0x800302c8` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800302c8` | `0x800302c8` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800302c8` | `0x80030328` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x800310e0` | `0x80031108` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031108` | `0x80031318` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031418` | `0x800314c4` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800314c4` | `0x80031548` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031548` | `0x800315c8` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800315c8` | `0x80031680` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031680` | `0x800316f4` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800316f4` | `0x800318b8` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800318b8` | `0x80031928` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031928` | `0x800319a0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x800319a0` | `0x80031b50` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031b50` | `0x80031bcc` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031bcc` | `0x80031c1c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031c1c` | `0x80031c6c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031c6c` | `0x80031c9c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031c9c` | `0x80031ce0` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031ce0` | `0x80031d24` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031d24` | `0x80031dd4` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031dd4` | `0x80031f30` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031f30` | `0x8003222c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003222c` | `0x80032408` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032408` | `0x800324b4` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800324b4` | `0x8003262c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x8003262c` | `0x800327f8` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800327f8` | `0x8003292c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032a1c` | `0x80032af8` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032af8` | `0x80032c48` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032c48` | `0x80032e24` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032fd4` | `0x800331c0` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800331c0` | `0x80033214` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033214` | `0x8003325c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8003325c` | `0x80033330` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033330` | `0x80033410` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033410` | `0x800335c8` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033fe0` | `0x8003405c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x8003405c` | `0x80034148` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800347ac` | `0x8003481c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x8003481c` | `0x8003487c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034c58` | `0x80034cac` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034e74` | `0x800350e0` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800350e0` | `0x80035420` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035420` | `0x800356d0` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800356d0` | `0x80035a04` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035a04` | `0x80035d8c` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035d8c` | `0x80035eac` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035ecc` | `0x800362fc` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800362fc` | `0x80036740` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036794` | `0x80036940` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036db4` | `0x80036f78` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037708` | `0x800379e0` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800382cc` | `0x8003835c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003835c` | `0x8003842c` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038604` | `0x80038660` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038850` | `0x80038abc` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038abc` | `0x80038ddc` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038ddc` | `0x8003908c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003908c` | `0x80039268` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039268` | `0x800395b0` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800396fc` | `0x8003af60` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003af60` | `0x8003c19c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c2c0` | `0x8003c3dc` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c3ec` | `0x8003c41c` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c41c` | `0x8003c9b8` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c9b8` | `0x8003ccc8` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ccc8` | `0x8003ccd0` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003ccd0` | `0x8003ccd4` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ccd4` | `0x8003ceb8` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cfb0` | `0x8003d1f8` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d1f8` | `0x8003d85c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d85c` | `0x8003d978` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d978` | `0x8003db90` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003db90` | `0x8003dbd0` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003dbd0` | `0x8003dc18` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003dc18` | `0x8003dc68` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003dc68` | `0x8003dcc0` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dcc0` | `0x8003dd20` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dd20` | `0x8003dd88` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dd88` | `0x8003ddf8` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003ddf8` | `0x8003de70` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003de70` | `0x8003def0` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003def0` | `0x8003df78` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003df78` | `0x8003e008` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e008` | `0x8003e0a0` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e0a0` | `0x8003e140` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e140` | `0x8003e1e8` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e1e8` | `0x8003e298` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e298` | `0x8003e350` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e350` | `0x8003e410` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e410` | `0x8003e4d8` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e4d8` | `0x8003e5a8` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e5a8` | `0x8003e680` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e680` | `0x8003e760` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e760` | `0x8003e848` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e848` | `0x8003e938` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e938` | `0x8003ea30` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ea30` | `0x8003eb30` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003eb30` | `0x8003ec38` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003ec38` | `0x8003ed48` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ed48` | `0x8003ee60` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ee60` | `0x8003ef80` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ef80` | `0x8003f0a8` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f0a8` | `0x8003f1d8` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f1d8` | `0x8003f310` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f310` | `0x8003f450` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f450` | `0x8003f4c8` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f4c8` | `0x8003f540` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f540` | `0x8003f5b8` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f5b8` | `0x8003f630` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f630` | `0x8003f6a8` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f6a8` | `0x8003f720` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f720` | `0x8003f798` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f798` | `0x8003f810` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f810` | `0x8003f888` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f888` | `0x8003f900` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f900` | `0x8003f978` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f978` | `0x8003f9f0` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f9f0` | `0x8003fa68` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003fa68` | `0x8003fae0` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003fae0` | `0x8003fb58` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fb58` | `0x8003fbd0` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fbd0` | `0x8003fc40` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fc40` | `0x8003fcb0` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fcb0` | `0x8003fd20` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fd20` | `0x8003fd90` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fd90` | `0x8003fe00` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fe00` | `0x8003fe70` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fe70` | `0x8003fee0` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fee0` | `0x8003ff50` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003ff50` | `0x8003ffc0` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003ffc0` | `0x80040030` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x80040030` | `0x800400a0` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x800400a0` | `0x80040110` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040110` | `0x80040180` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040180` | `0x800401f0` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800401f0` | `0x80040260` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040260` | `0x800402d0` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800402d0` | `0x800402e8` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800402e8` | `0x800402fc` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800402fc` | `0x80040388` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040388` | `0x800403a0` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800403a0` | `0x800403b4` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800403b4` | `0x8004043c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8004043c` | `0x80040454` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040454` | `0x80040468` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040468` | `0x80040488` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040488` | `0x80040490` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040490` | `0x8004049c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8004049c` | `0x800404a0` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800404a0` | `0x80040524` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040524` | `0x800405cc` | 168 | `h_ADD` | UNCONVERTED |
| `0x800405cc` | `0x80040700` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040700` | `0x800407a8` | 168 | `h_SUB` | UNCONVERTED |
| `0x800407a8` | `0x800408a0` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x800408a0` | `0x80040938` | 152 | `h_LT` | UNCONVERTED |
| `0x80040938` | `0x800409d0` | 152 | `h_GT` | UNCONVERTED |
| `0x800409d0` | `0x80040a64` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040a64` | `0x80040af8` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040af8` | `0x80040b7c` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040b7c` | `0x80040bdc` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040bdc` | `0x80040c50` | 116 | `h_AND` | UNCONVERTED |
| `0x80040c50` | `0x80040cc4` | 116 | `h_OR` | UNCONVERTED |
| `0x80040cc4` | `0x80040d38` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040d38` | `0x80040d98` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040d98` | `0x80040e84` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040e84` | `0x80041024` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041024` | `0x800411c4` | 416 | `h_SHR` | UNCONVERTED |
| `0x800411c4` | `0x80041378` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041378` | `0x80041478` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041478` | `0x800414ac` | 52 | `h_POP` | UNCONVERTED |
| `0x800414ac` | `0x800417f8` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800417f8` | `0x80041ad8` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041ad8` | `0x80041bf8` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041bf8` | `0x80041c3c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041c3c` | `0x80041c80` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041c80` | `0x80041cd0` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041cd0` | `0x80041d20` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041d20` | `0x80041d70` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041d70` | `0x80041dc0` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041dc0` | `0x80041e10` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041e10` | `0x80041e60` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041e60` | `0x80041eb0` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041eb0` | `0x80041f00` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041f00` | `0x80041f50` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041f50` | `0x80041fa0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041fa0` | `0x80041ff0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041ff0` | `0x80042040` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042040` | `0x80042090` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042090` | `0x800420e0` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800420e0` | `0x80042130` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042130` | `0x800421c8` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800421c8` | `0x800422b4` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800422b4` | `0x800422f8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800422f8` | `0x80042514` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042514` | `0x800426e4` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800426e4` | `0x80042728` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042728` | `0x800428f4` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800428f4` | `0x800428fc` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800428fc` | `0x800429bc` | 192 | `h_JUMP` | UNCONVERTED |
| `0x800429bc` | `0x80042ab0` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042ab0` | `0x80042af4` | 68 | `h_PC` | UNCONVERTED |
| `0x80042af4` | `0x80042d7c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042d7c` | `0x80043070` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80043070` | `0x80043384` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043384` | `0x800436b8` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800436b8` | `0x80043a0c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043a0c` | `0x80043d80` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043d80` | `0x80044028` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044028` | `0x80044330` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044330` | `0x8004499c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004499c` | `0x80044f44` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044f44` | `0x800454c4` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800454c4` | `0x80045d50` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045d50` | `0x80045e3c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045e3c` | `0x80045f0c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045f0c` | `0x8004618c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x8004618c` | `0x80046b24` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046b24` | `0x80047108` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047108` | `0x80047124` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047124` | `0x80048648` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048648` | `0x80048694` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048694` | `0x80048838` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048838` | `0x80049600` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049600` | `0x8004b8ac` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b8ac` | `0x8004ca24` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004ca24` | `0x8004d688` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d688` | `0x8004e490` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e490` | `0x8004f0f4` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f0f4` | `0x8004f9ac` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f9ac` | `0x800502a0` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800502a0` | `0x8005083c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8005083c` | `0x80050ee8` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050ee8` | `0x80050f08` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050f08` | `0x800515b4` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800515b4` | `0x800515d4` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800515d4` | `0x80051f04` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051f04` | `0x80052250` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052250` | `0x800523c0` | 368 | `h_STOP` | UNCONVERTED |
| `0x800523c0` | `0x800523c4` | 4 | `h_invalid` | UNCONVERTED |
| `0x800523c4` | `0x8005244c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005244c` | `0x80052640` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052640` | `0x80052670` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052670` | `0x80052684` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052684` | `0x80052694` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052694` | `0x800526c4` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800526c4` | `0x800528b8` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x800528b8` | `0x800528e8` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800528e8` | `0x800528fc` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800528fc` | `0x8005290c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x8005290c` | `0x8005293c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x8005293c` | `0x80052960` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052960` | `0x80052990` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052990` | `0x80052b84` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052b84` | `0x80052bb4` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052bb4` | `0x80052bc8` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bc8` | `0x80052bd8` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052bd8` | `0x80052c08` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052c08` | `0x80052dfc` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052dfc` | `0x80052e2c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052e2c` | `0x80052e40` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e40` | `0x80052e50` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052e50` | `0x80052e80` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e80` | `0x80053074` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053074` | `0x800530a4` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800530a4` | `0x800530b8` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800530b8` | `0x800530c8` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800530c8` | `0x800530f8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800530f8` | `0x800530f8` | 0 | `.exit_label` | UNCONVERTED |
| `0x800530f8` | `0x80053114` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800532a0` | `0x800534d4` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800539d4` | `0x80053b04` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053b04` | `0x80053b60` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053b60` | `0x80053b80` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053b80` | `0x80053cbc` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053e8c` | `0x80053e98` | 12 | `requests_hash_verify` | TAIL |
