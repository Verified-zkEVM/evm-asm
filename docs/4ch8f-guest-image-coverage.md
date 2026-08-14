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

`.text` = [0x80000000, 0x80053e94), 343700 bytes (`RegionMap.textSizeBytes = 0x53e94`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121724 bytes (35.42%)
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
| `0x8002c494` | `0x8002c98c` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c98c` | `0x8002d5b0` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d5b0` | `0x8002db80` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002db80` | `0x8002f540` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f540` | `0x8002f564` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f564` | `0x8002f580` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f580` | `0x8002f844` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f844` | `0x8002f854` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f854` | `0x8002f888` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f888` | `0x8002f8a0` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f8a0` | `0x8002f8b0` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f8b0` | `0x8002f8e4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f8e4` | `0x8002f8ec` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f8ec` | `0x8002f998` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f998` | `0x8002f9a4` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f9a4` | `0x8002f9cc` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f9cc` | `0x8002fa0c` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002fa0c` | `0x8002fa3c` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002fa3c` | `0x8002fa3c` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002fa3c` | `0x8002fa54` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fa54` | `0x8002fa5c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fa5c` | `0x8002fa68` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002fa68` | `0x8002fa80` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fa80` | `0x8002fa98` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fa98` | `0x8002faac` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002faac` | `0x8002facc` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002facc` | `0x8002fae0` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002fae0` | `0x8002fb0c` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fb0c` | `0x8002fb54` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fb54` | `0x8002fc34` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fc34` | `0x8002fce4` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fce4` | `0x8002fd04` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fd04` | `0x8002fd78` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fd78` | `0x8002fd88` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fd88` | `0x8002fd94` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fd94` | `0x8002fe78` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fe78` | `0x8002fea0` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fea0` | `0x8002feb4` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002feb4` | `0x8002feb4` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002feb4` | `0x8002feb4` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002feb4` | `0x8002fed4` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fed4` | `0x8002ff04` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002ff04` | `0x8002ff28` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002ff28` | `0x8002ff48` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002ff48` | `0x8002ff4c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002ff4c` | `0x8002ffd8` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002ffd8` | `0x8002ffe8` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002ffe8` | `0x8002fff8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fff8` | `0x80030128` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x80030128` | `0x80030128` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x80030128` | `0x800302c4` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800302c4` | `0x800302c4` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800302c4` | `0x80030324` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x800310dc` | `0x80031104` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031104` | `0x80031314` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031414` | `0x800314c0` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800314c0` | `0x80031544` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031544` | `0x800315c4` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800315c4` | `0x8003167c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x8003167c` | `0x800316f0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800316f0` | `0x800318b4` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800318b4` | `0x80031924` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031924` | `0x8003199c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x8003199c` | `0x80031b4c` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031b4c` | `0x80031bc8` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031bc8` | `0x80031c18` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031c18` | `0x80031c68` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031c68` | `0x80031c98` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031c98` | `0x80031cdc` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031cdc` | `0x80031d20` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031d20` | `0x80031dd0` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031dd0` | `0x80031f2c` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031f2c` | `0x80032228` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80032228` | `0x80032404` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032404` | `0x800324b0` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800324b0` | `0x80032628` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032628` | `0x800327f4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800327f4` | `0x80032928` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032a18` | `0x80032af4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032af4` | `0x80032c44` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032c44` | `0x80032e20` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032fd0` | `0x800331bc` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800331bc` | `0x80033210` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033210` | `0x80033258` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033258` | `0x8003332c` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x8003332c` | `0x8003340c` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x8003340c` | `0x800335c4` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033fdc` | `0x80034058` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034058` | `0x80034144` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800347a8` | `0x80034818` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034818` | `0x80034878` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034c54` | `0x80034ca8` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034e70` | `0x800350dc` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800350dc` | `0x8003541c` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x8003541c` | `0x800356cc` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800356cc` | `0x80035a00` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035a00` | `0x80035d88` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035d88` | `0x80035ea8` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035ec8` | `0x800362f8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800362f8` | `0x8003673c` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036790` | `0x8003693c` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036db0` | `0x80036f74` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037704` | `0x800379dc` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800382c8` | `0x80038358` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038358` | `0x80038428` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038600` | `0x8003865c` | 92 | `blq_sub` | UNCONVERTED |
| `0x8003884c` | `0x80038ab8` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038ab8` | `0x80038dd8` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038dd8` | `0x80039088` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039088` | `0x80039264` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039264` | `0x800395ac` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800396f8` | `0x8003af5c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003af5c` | `0x8003c198` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c2bc` | `0x8003c3d8` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c3e8` | `0x8003c418` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c418` | `0x8003c9b4` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c9b4` | `0x8003ccc4` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ccc4` | `0x8003cccc` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cccc` | `0x8003ccd0` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ccd0` | `0x8003ceb4` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cfac` | `0x8003d1f4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d1f4` | `0x8003d858` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d858` | `0x8003d974` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d974` | `0x8003db8c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003db8c` | `0x8003dbcc` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003dbcc` | `0x8003dc14` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003dc14` | `0x8003dc64` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003dc64` | `0x8003dcbc` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dcbc` | `0x8003dd1c` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dd1c` | `0x8003dd84` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dd84` | `0x8003ddf4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003ddf4` | `0x8003de6c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003de6c` | `0x8003deec` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003deec` | `0x8003df74` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003df74` | `0x8003e004` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e004` | `0x8003e09c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e09c` | `0x8003e13c` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e13c` | `0x8003e1e4` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e1e4` | `0x8003e294` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e294` | `0x8003e34c` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e34c` | `0x8003e40c` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e40c` | `0x8003e4d4` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e4d4` | `0x8003e5a4` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e5a4` | `0x8003e67c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e67c` | `0x8003e75c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e75c` | `0x8003e844` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e844` | `0x8003e934` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e934` | `0x8003ea2c` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ea2c` | `0x8003eb2c` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003eb2c` | `0x8003ec34` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003ec34` | `0x8003ed44` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ed44` | `0x8003ee5c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ee5c` | `0x8003ef7c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ef7c` | `0x8003f0a4` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f0a4` | `0x8003f1d4` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f1d4` | `0x8003f30c` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f30c` | `0x8003f44c` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f44c` | `0x8003f4c4` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f4c4` | `0x8003f53c` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f53c` | `0x8003f5b4` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f5b4` | `0x8003f62c` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f62c` | `0x8003f6a4` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f6a4` | `0x8003f71c` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f71c` | `0x8003f794` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f794` | `0x8003f80c` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f80c` | `0x8003f884` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f884` | `0x8003f8fc` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f8fc` | `0x8003f974` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f974` | `0x8003f9ec` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f9ec` | `0x8003fa64` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003fa64` | `0x8003fadc` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003fadc` | `0x8003fb54` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fb54` | `0x8003fbcc` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fbcc` | `0x8003fc3c` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fc3c` | `0x8003fcac` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fcac` | `0x8003fd1c` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fd1c` | `0x8003fd8c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fd8c` | `0x8003fdfc` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fdfc` | `0x8003fe6c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fe6c` | `0x8003fedc` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fedc` | `0x8003ff4c` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003ff4c` | `0x8003ffbc` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003ffbc` | `0x8004002c` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8004002c` | `0x8004009c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004009c` | `0x8004010c` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8004010c` | `0x8004017c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004017c` | `0x800401ec` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800401ec` | `0x8004025c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004025c` | `0x800402cc` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800402cc` | `0x800402e4` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800402e4` | `0x800402f8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800402f8` | `0x80040384` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040384` | `0x8004039c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004039c` | `0x800403b0` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800403b0` | `0x80040438` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040438` | `0x80040450` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040450` | `0x80040464` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040464` | `0x80040484` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040484` | `0x8004048c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004048c` | `0x80040498` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040498` | `0x8004049c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004049c` | `0x80040520` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040520` | `0x800405c8` | 168 | `h_ADD` | UNCONVERTED |
| `0x800405c8` | `0x800406fc` | 308 | `h_MUL` | UNCONVERTED |
| `0x800406fc` | `0x800407a4` | 168 | `h_SUB` | UNCONVERTED |
| `0x800407a4` | `0x8004089c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8004089c` | `0x80040934` | 152 | `h_LT` | UNCONVERTED |
| `0x80040934` | `0x800409cc` | 152 | `h_GT` | UNCONVERTED |
| `0x800409cc` | `0x80040a60` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040a60` | `0x80040af4` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040af4` | `0x80040b78` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040b78` | `0x80040bd8` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040bd8` | `0x80040c4c` | 116 | `h_AND` | UNCONVERTED |
| `0x80040c4c` | `0x80040cc0` | 116 | `h_OR` | UNCONVERTED |
| `0x80040cc0` | `0x80040d34` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040d34` | `0x80040d94` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040d94` | `0x80040e80` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040e80` | `0x80041020` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041020` | `0x800411c0` | 416 | `h_SHR` | UNCONVERTED |
| `0x800411c0` | `0x80041374` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041374` | `0x80041474` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041474` | `0x800414a8` | 52 | `h_POP` | UNCONVERTED |
| `0x800414a8` | `0x800417f4` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800417f4` | `0x80041ad4` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041ad4` | `0x80041bf4` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041bf4` | `0x80041c38` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041c38` | `0x80041c7c` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041c7c` | `0x80041ccc` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041ccc` | `0x80041d1c` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041d1c` | `0x80041d6c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041d6c` | `0x80041dbc` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041dbc` | `0x80041e0c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041e0c` | `0x80041e5c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041e5c` | `0x80041eac` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041eac` | `0x80041efc` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041efc` | `0x80041f4c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041f4c` | `0x80041f9c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041f9c` | `0x80041fec` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041fec` | `0x8004203c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x8004203c` | `0x8004208c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004208c` | `0x800420dc` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800420dc` | `0x8004212c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x8004212c` | `0x800421c4` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800421c4` | `0x800422b0` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800422b0` | `0x800422f4` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800422f4` | `0x80042510` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042510` | `0x800426e0` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800426e0` | `0x80042724` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042724` | `0x800428f0` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800428f0` | `0x800428f8` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800428f8` | `0x800429b8` | 192 | `h_JUMP` | UNCONVERTED |
| `0x800429b8` | `0x80042aac` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042aac` | `0x80042af0` | 68 | `h_PC` | UNCONVERTED |
| `0x80042af0` | `0x80042d78` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042d78` | `0x8004306c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004306c` | `0x80043380` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043380` | `0x800436b4` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800436b4` | `0x80043a08` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043a08` | `0x80043d7c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043d7c` | `0x80044024` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044024` | `0x8004432c` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8004432c` | `0x80044998` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044998` | `0x80044f40` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044f40` | `0x800454c0` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800454c0` | `0x80045d4c` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045d4c` | `0x80045e38` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045e38` | `0x80045f08` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045f08` | `0x80046188` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046188` | `0x80046b20` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046b20` | `0x80047104` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047104` | `0x80047120` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047120` | `0x80048644` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048644` | `0x80048690` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048690` | `0x80048834` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048834` | `0x800495fc` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800495fc` | `0x8004b8a8` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b8a8` | `0x8004ca20` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004ca20` | `0x8004d684` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d684` | `0x8004e48c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e48c` | `0x8004f0f0` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f0f0` | `0x8004f9a8` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f9a8` | `0x8005029c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005029c` | `0x80050838` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050838` | `0x80050ee4` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050ee4` | `0x80050f04` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050f04` | `0x800515b0` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800515b0` | `0x800515d0` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800515d0` | `0x80051f00` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051f00` | `0x8005224c` | 844 | `h_EXP` | UNCONVERTED |
| `0x8005224c` | `0x800523bc` | 368 | `h_STOP` | UNCONVERTED |
| `0x800523bc` | `0x800523c0` | 4 | `h_invalid` | UNCONVERTED |
| `0x800523c0` | `0x80052448` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80052448` | `0x8005263c` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x8005263c` | `0x8005266c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005266c` | `0x80052680` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052680` | `0x80052690` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052690` | `0x800526c0` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800526c0` | `0x800528b4` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x800528b4` | `0x800528e4` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800528e4` | `0x800528f8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800528f8` | `0x80052908` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052908` | `0x80052938` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052938` | `0x8005295c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x8005295c` | `0x8005298c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x8005298c` | `0x80052b80` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052b80` | `0x80052bb0` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052bb0` | `0x80052bc4` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bc4` | `0x80052bd4` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052bd4` | `0x80052c04` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052c04` | `0x80052df8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052df8` | `0x80052e28` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052e28` | `0x80052e3c` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e3c` | `0x80052e4c` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052e4c` | `0x80052e7c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e7c` | `0x80053070` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053070` | `0x800530a0` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800530a0` | `0x800530b4` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800530b4` | `0x800530c4` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800530c4` | `0x800530f4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800530f4` | `0x800530f4` | 0 | `.exit_label` | UNCONVERTED |
| `0x800530f4` | `0x80053110` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005329c` | `0x800534d0` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800539d0` | `0x80053b00` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053b00` | `0x80053b5c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053b5c` | `0x80053b7c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053b7c` | `0x80053cb8` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053e88` | `0x80053e94` | 12 | `requests_hash_verify` | TAIL |
