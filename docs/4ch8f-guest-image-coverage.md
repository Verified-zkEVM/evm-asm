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
not linked** (42 of 373 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053454), 341076 bytes (`RegionMap.textSizeBytes = 0x53454`)

- symbols in `.text`: 905 (331 converted, 574 unconverted)
- covered by converted `_prog`s: 80928 bytes (23.73%)
- NOT covered: 260148 bytes (76.27%), 575 ranges

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
| `0x80004f78` | `0x80004fac` | 52 | `rlp_walk_next` | UNCONVERTED |
| `0x80004fac` | `0x80004fb0` | 4 | `rlp_walk_next_nested` | UNCONVERTED |
| `0x80004fb0` | `0x80005080` | 208 | `rlp_walk_next_shared` | UNCONVERTED |
| `0x80005080` | `0x800050dc` | 92 | `rlp_validate_payload` | UNCONVERTED |
| `0x800050dc` | `0x80005278` | 412 | `rlp_walk_next_core` | UNCONVERTED |
| `0x80005278` | `0x800052c0` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x800052c0` | `0x80005328` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x80005328` | `0x80005380` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x80005380` | `0x800053e8` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x800053e8` | `0x800055dc` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x8000989c` | `0x80009a60` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009a60` | `0x80009acc` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a18c` | `0x8000a388` | 508 | `mpt_indexed_stream_leaf_hash` | UNCONVERTED |
| `0x8000a388` | `0x8000a588` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a588` | `0x8000a6c8` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a6c8` | `0x8000a984` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a984` | `0x8000aa74` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000aa74` | `0x8000abe4` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000bb18` | `0x8000c0a8` | 1424 | `block_header_ssz_to_rlp` | UNCONVERTED |
| `0x8000de94` | `0x8000f1b0` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f5e0` | `0x8000f7c0` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f7c0` | `0x8000f8a4` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f8a4` | `0x8000f980` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f980` | `0x8000fa14` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fa14` | `0x8000fad0` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fad0` | `0x8000fb80` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fb80` | `0x8000fc64` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000fc64` | `0x8000fca0` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000fca0` | `0x8000fdd0` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000fdd0` | `0x8000fef4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000fef4` | `0x8000ffa4` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000ffa4` | `0x80010120` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010120` | `0x800101f8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800101f8` | `0x80010388` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010388` | `0x80010524` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010524` | `0x800105d4` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800105d4` | `0x8001063c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8001063c` | `0x800106d8` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800106d8` | `0x80010d0c` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010d0c` | `0x80010ff4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010ff4` | `0x8001134c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001134c` | `0x80011828` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011828` | `0x80011acc` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011acc` | `0x80011be8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011be8` | `0x80011ea0` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011ea0` | `0x800120c0` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800120c0` | `0x80012458` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012458` | `0x8001256c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001256c` | `0x8001258c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001258c` | `0x80012814` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012814` | `0x800128f8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800128f8` | `0x800129a0` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800129a0` | `0x800130d4` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800130d4` | `0x8001370c` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001370c` | `0x800138dc` | 464 | `chain_config_valid` | UNCONVERTED |
| `0x800138dc` | `0x80013a48` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80013a48` | `0x80013a5c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013a5c` | `0x80013a68` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013a68` | `0x80013ab8` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013ab8` | `0x80013ad8` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013ad8` | `0x80013b3c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013b3c` | `0x80013de4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013de4` | `0x80014038` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014038` | `0x800141ec` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800141ec` | `0x800145fc` | 1040 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80014dec` | `0x80014fe4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015304` | `0x80015534` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015630` | `0x80015924` | 756 | `simple_transfer_intrinsic_gas` | UNCONVERTED |
| `0x80015924` | `0x8001844c` | 11048 | `block_verdict` | UNCONVERTED |
| `0x8001844c` | `0x800191c4` | 3448 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800191c4` | `0x800193e0` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800196c8` | `0x8001975c` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019f54` | `0x8001a1ac` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a1ac` | `0x8001a424` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a424` | `0x8001a6b8` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a8f4` | `0x8001aa94` | 416 | `bal_gas_valid_from_builder` | UNCONVERTED |
| `0x8001aca8` | `0x8001af60` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b328` | `0x8001b49c` | 372 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b49c` | `0x8001b63c` | 416 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b63c` | `0x8001c118` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c420` | `0x8001c468` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c59c` | `0x8001c964` | 968 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001c964` | `0x8001c9f4` | 144 | `stage_runtime_payload_witness_context` | UNCONVERTED |
| `0x8001c9f4` | `0x8001cbdc` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001cbdc` | `0x8001cc38` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001cc38` | `0x8001cd04` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001cd04` | `0x8001cdd8` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cdd8` | `0x8001dd00` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e5d4` | `0x8001e6e8` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e6e8` | `0x8001e9f0` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f188` | `0x8001f2dc` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8001f6a4` | `0x8001f6e4` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f6e4` | `0x8001f944` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x8001f944` | `0x8001fa8c` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001fa8c` | `0x8001fabc` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001fabc` | `0x8001fc4c` | 400 | `storage_read_record` | UNCONVERTED |
| `0x8001fc4c` | `0x8001fdc8` | 380 | `storage_read_record_block` | UNCONVERTED |
| `0x8001fdc8` | `0x8002000c` | 580 | `storage_write_record` | UNCONVERTED |
| `0x8002000c` | `0x8002019c` | 400 | `destroy_storage` | UNCONVERTED |
| `0x8002019c` | `0x80020340` | 420 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x80020340` | `0x80020400` | 192 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x80020400` | `0x80020428` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x80020428` | `0x80020524` | 252 | `storage_writes_undo_push` | UNCONVERTED |
| `0x80020524` | `0x80020668` | 324 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80020668` | `0x800208a8` | 576 | `account_write_record` | UNCONVERTED |
| `0x800208a8` | `0x800209e8` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x800209e8` | `0x80020ab0` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x80020ab0` | `0x80020b60` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x80020b60` | `0x80020c10` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80020c10` | `0x80020d80` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x80020d80` | `0x80020e8c` | 268 | `account_writes_auth_block` | UNCONVERTED |
| `0x80020e8c` | `0x80020f30` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x80020f30` | `0x800210bc` | 396 | `account_writes_lookup_current` | UNCONVERTED |
| `0x800210bc` | `0x80021390` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x80021390` | `0x800214ac` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800214ac` | `0x80021670` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021670` | `0x80021900` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021900` | `0x80021950` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x80021950` | `0x80021a44` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x80021a44` | `0x80021f48` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x80021f48` | `0x80021fd4` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x80021fd4` | `0x800220f4` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800220f4` | `0x800221f8` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x800221f8` | `0x800223b4` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x800223b4` | `0x80022810` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x80022810` | `0x80022ab8` | 680 | `bal_map_final_value_matches` | UNCONVERTED |
| `0x80022ab8` | `0x80022ba8` | 240 | `bal_map_builder_consistent` | UNCONVERTED |
| `0x80022df4` | `0x80022e10` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022e10` | `0x80022e84` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022e84` | `0x80022ed4` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022ed4` | `0x80022f00` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022f00` | `0x80022fe0` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022fe0` | `0x80023060` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023060` | `0x80023090` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023090` | `0x800231d0` | 320 | `bal_rlp_emit_bytes` | UNCONVERTED |
| `0x800231d0` | `0x80023294` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023294` | `0x800232e8` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800232e8` | `0x80023318` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023318` | `0x80023358` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023358` | `0x80023390` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023390` | `0x800233d0` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800233d0` | `0x8002348c` | 188 | `bal_serializer_slot_written` | UNCONVERTED |
| `0x8002348c` | `0x80023530` | 164 | `bal_serializer_slot_seen_before` | UNCONVERTED |
| `0x80023530` | `0x80023548` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80023548` | `0x80023624` | 220 | `bal_serializer_measure_reads` | UNCONVERTED |
| `0x80023624` | `0x80023654` | 48 | `bal_serializer_slot_to_le` | UNCONVERTED |
| `0x80023654` | `0x80023684` | 48 | `bal_serializer_balance_to_le` | UNCONVERTED |
| `0x80023684` | `0x80023790` | 268 | `bal_serializer_measure_slot` | UNCONVERTED |
| `0x80023790` | `0x80023870` | 224 | `bal_serializer_measure_storage` | UNCONVERTED |
| `0x80023870` | `0x8002394c` | 220 | `bal_serializer_measure_balance` | UNCONVERTED |
| `0x8002394c` | `0x80023a34` | 232 | `bal_serializer_measure_nonce` | UNCONVERTED |
| `0x80023a34` | `0x80023b24` | 240 | `bal_serializer_measure_code` | UNCONVERTED |
| `0x80023b24` | `0x80023c08` | 228 | `bal_serializer_measure_account` | UNCONVERTED |
| `0x80023c08` | `0x80023de8` | 480 | `bal_serializer_emit_storage` | UNCONVERTED |
| `0x80023de8` | `0x80023eb4` | 204 | `bal_serializer_emit_reads` | UNCONVERTED |
| `0x80023eb4` | `0x80023ff8` | 324 | `bal_serializer_emit_balance` | UNCONVERTED |
| `0x80023ff8` | `0x80024170` | 376 | `bal_serializer_emit_nonce` | UNCONVERTED |
| `0x80024170` | `0x800242a4` | 308 | `bal_serializer_emit_code` | UNCONVERTED |
| `0x800242a4` | `0x800243d0` | 300 | `bal_serializer_emit_account` | UNCONVERTED |
| `0x800243d0` | `0x80024460` | 144 | `bal_serializer_measure_outer` | UNCONVERTED |
| `0x80024460` | `0x80024508` | 168 | `bal_serializer_emit_outer` | UNCONVERTED |
| `0x80024508` | `0x80024704` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024704` | `0x8002479c` | 152 | `bal_serializer_verify` | UNCONVERTED |
| `0x8002479c` | `0x800248a8` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800248a8` | `0x8002490c` | 100 | `bal_builder_incorporate_touched_accounts` | UNCONVERTED |
| `0x8002490c` | `0x80024ad4` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024ad4` | `0x80024dbc` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024dbc` | `0x80024ea4` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024ea4` | `0x80024f80` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024f80` | `0x80025058` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025058` | `0x8002517c` | 292 | `account_read_record` | UNCONVERTED |
| `0x8002517c` | `0x800251d0` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x800251d0` | `0x80025330` | 352 | `code_read_record` | UNCONVERTED |
| `0x80025330` | `0x800253dc` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x800253dc` | `0x80025500` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025500` | `0x800255f8` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800255f8` | `0x80025620` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x80025620` | `0x80025748` | 296 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80025b9c` | `0x80025dcc` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80025dcc` | `0x80025ddc` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025fc0` | `0x800261d8` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x800261d8` | `0x800263cc` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026760` | `0x80026de4` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027b64` | `0x80027c9c` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80027c9c` | `0x80027d00` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x80027d00` | `0x8002821c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x8002827c` | `0x8002831c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800286c4` | `0x8002881c` | 344 | `eip7702_authorization_extract_signature` | UNCONVERTED |
| `0x800289d4` | `0x80028b64` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x80028b64` | `0x80028ee0` | 892 | `eip7702_authority_asof` | UNCONVERTED |
| `0x80028ee0` | `0x800296d4` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x800296d4` | `0x80029a0c` | 824 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x80029a0c` | `0x80029afc` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x80029d68` | `0x8002a004` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a004` | `0x8002a03c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002a404` | `0x8002a4f0` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002a640` | `0x8002a7d4` | 404 | `tx_legacy_extract_signature` | UNCONVERTED |
| `0x8002a7d4` | `0x8002a990` | 444 | `tx_eip2930_extract_signature` | UNCONVERTED |
| `0x8002a990` | `0x8002ab60` | 464 | `tx_eip1559_extract_signature` | UNCONVERTED |
| `0x8002ab60` | `0x8002ad58` | 504 | `tx_eip4844_extract_signature` | UNCONVERTED |
| `0x8002ad58` | `0x8002af3c` | 484 | `tx_eip7702_extract_signature` | UNCONVERTED |
| `0x8002bc34` | `0x8002c124` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c124` | `0x8002cb70` | 2636 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cb70` | `0x8002d140` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d140` | `0x8002eb00` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002eb00` | `0x8002eb24` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002eb24` | `0x8002eb40` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002eb40` | `0x8002ee04` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002ee04` | `0x8002ee14` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002ee14` | `0x8002ee48` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002ee48` | `0x8002ee60` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002ee60` | `0x8002ee70` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002ee70` | `0x8002eea4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002eea4` | `0x8002eeac` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002eeac` | `0x8002ef58` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ef58` | `0x8002ef64` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ef64` | `0x8002ef8c` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ef8c` | `0x8002efcc` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002efcc` | `0x8002effc` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002effc` | `0x8002effc` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002effc` | `0x8002f014` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f014` | `0x8002f01c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f01c` | `0x8002f028` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f028` | `0x8002f040` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f040` | `0x8002f058` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f058` | `0x8002f06c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f06c` | `0x8002f08c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f08c` | `0x8002f0a0` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f0a0` | `0x8002f0cc` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f0cc` | `0x8002f114` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f114` | `0x8002f1f4` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f1f4` | `0x8002f2a4` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f2a4` | `0x8002f2c4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f2c4` | `0x8002f338` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f338` | `0x8002f348` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f348` | `0x8002f354` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f354` | `0x8002f438` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f438` | `0x8002f460` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f460` | `0x8002f474` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f474` | `0x8002f474` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f474` | `0x8002f474` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f474` | `0x8002f494` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f494` | `0x8002f4c4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f4c4` | `0x8002f4e8` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f4e8` | `0x8002f508` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f508` | `0x8002f50c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f50c` | `0x8002f598` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f598` | `0x8002f5a8` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f5a8` | `0x8002f5b8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f5b8` | `0x8002f6e8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f6e8` | `0x8002f6e8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f6e8` | `0x8002f884` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002f884` | `0x8002f8e4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8002f8e4` | `0x8002fa3c` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x8003069c` | `0x800306c4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800306c4` | `0x800308d4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030934` | `0x800309d4` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x800309d4` | `0x80030a80` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030a80` | `0x80030b04` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030b04` | `0x80030b84` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030b84` | `0x80030c3c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030c3c` | `0x80030cb0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030cb0` | `0x80030e74` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80030e74` | `0x80030ee4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80030ee4` | `0x80030f5c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80030f5c` | `0x8003110c` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x8003110c` | `0x80031188` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031188` | `0x800311d8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800311d8` | `0x80031228` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031228` | `0x80031258` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031258` | `0x8003129c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x8003129c` | `0x800312e0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800312e0` | `0x80031390` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031390` | `0x800314ec` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800314ec` | `0x800317e8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800317e8` | `0x800319c4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800319c4` | `0x80031a70` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031a70` | `0x80031be8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031be8` | `0x80031db4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031db4` | `0x80031ee8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80031fd8` | `0x800320b4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800320b4` | `0x80032204` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032204` | `0x800323e0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032590` | `0x8003277c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003277c` | `0x800327d0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800327d0` | `0x80032818` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032818` | `0x800328ec` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800328ec` | `0x800329cc` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800329cc` | `0x80032b84` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80032b84` | `0x80032ca0` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x80033320` | `0x800333fc` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x800333fc` | `0x8003356c` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x8003359c` | `0x80033618` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033618` | `0x80033704` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033d68` | `0x80033dd8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033dd8` | `0x80033e38` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034084` | `0x80034214` | 400 | `bnq_mul` | UNCONVERTED |
| `0x80034214` | `0x80034268` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034430` | `0x8003469c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x8003469c` | `0x800349dc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800349dc` | `0x80034c8c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034c8c` | `0x80034fc0` | 820 | `bng2_double` | UNCONVERTED |
| `0x80034fc0` | `0x80035348` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035348` | `0x80035468` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035488` | `0x800358b8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800358b8` | `0x80035cfc` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035d50` | `0x80035efc` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x8003601c` | `0x800361e4` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80036370` | `0x80036534` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036cc4` | `0x80036f9c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037370` | `0x80037480` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80037480` | `0x800375d4` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x800375d4` | `0x8003770c` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037888` | `0x80037918` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037918` | `0x800379e8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800379e8` | `0x80037bc0` | 472 | `blq_mul` | UNCONVERTED |
| `0x80037bc0` | `0x80037c1c` | 92 | `blq_sub` | UNCONVERTED |
| `0x80037e0c` | `0x80038078` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038078` | `0x80038398` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038398` | `0x80038648` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038648` | `0x80038824` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038824` | `0x80038b6c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038cb8` | `0x8003a51c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a51c` | `0x8003b758` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003b7d8` | `0x8003b87c` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003b87c` | `0x8003b998` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003b9a8` | `0x8003b9d8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003b9d8` | `0x8003bf74` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003bf74` | `0x8003c284` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c284` | `0x8003c28c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c28c` | `0x8003c290` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c290` | `0x8003c474` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c504` | `0x8003c56c` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003c56c` | `0x8003c7b4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c7b4` | `0x8003ce18` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ce18` | `0x8003cf34` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003cf34` | `0x8003d14c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d14c` | `0x8003d18c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d18c` | `0x8003d1d4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d1d4` | `0x8003d224` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d224` | `0x8003d27c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d27c` | `0x8003d2dc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d2dc` | `0x8003d344` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d344` | `0x8003d3b4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d3b4` | `0x8003d42c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d42c` | `0x8003d4ac` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d4ac` | `0x8003d534` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d534` | `0x8003d5c4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d5c4` | `0x8003d65c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d65c` | `0x8003d6fc` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d6fc` | `0x8003d7a4` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d7a4` | `0x8003d854` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003d854` | `0x8003d90c` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003d90c` | `0x8003d9cc` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003d9cc` | `0x8003da94` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003da94` | `0x8003db64` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003db64` | `0x8003dc3c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003dc3c` | `0x8003dd1c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003dd1c` | `0x8003de04` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003de04` | `0x8003def4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003def4` | `0x8003dfec` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003dfec` | `0x8003e0ec` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e0ec` | `0x8003e1f4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e1f4` | `0x8003e304` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e304` | `0x8003e41c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e41c` | `0x8003e53c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e53c` | `0x8003e664` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e664` | `0x8003e794` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e794` | `0x8003e8cc` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003e8cc` | `0x8003ea0c` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003ea0c` | `0x8003ea84` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ea84` | `0x8003eafc` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003eafc` | `0x8003eb74` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003eb74` | `0x8003ebec` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ebec` | `0x8003ec64` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ec64` | `0x8003ecdc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003ecdc` | `0x8003ed54` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ed54` | `0x8003edcc` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003edcc` | `0x8003ee44` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003ee44` | `0x8003eebc` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003eebc` | `0x8003ef34` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ef34` | `0x8003efac` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003efac` | `0x8003f024` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f024` | `0x8003f09c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f09c` | `0x8003f114` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f114` | `0x8003f18c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f18c` | `0x8003f1fc` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f1fc` | `0x8003f26c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f26c` | `0x8003f2dc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f2dc` | `0x8003f34c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f34c` | `0x8003f3bc` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f3bc` | `0x8003f42c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f42c` | `0x8003f49c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f49c` | `0x8003f50c` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f50c` | `0x8003f57c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f57c` | `0x8003f5ec` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f5ec` | `0x8003f65c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f65c` | `0x8003f6cc` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f6cc` | `0x8003f73c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f73c` | `0x8003f7ac` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f7ac` | `0x8003f81c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003f81c` | `0x8003f88c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003f88c` | `0x8003f8a4` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003f8a4` | `0x8003f8b8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003f8b8` | `0x8003f944` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003f944` | `0x8003f95c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003f95c` | `0x8003f970` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003f970` | `0x8003f9f8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003f9f8` | `0x8003fa10` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003fa10` | `0x8003fa24` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003fa24` | `0x8003fa44` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003fa44` | `0x8003fa4c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003fa4c` | `0x8003fa58` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003fa58` | `0x8003fa5c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003fa5c` | `0x8003fae0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fae0` | `0x8003fb88` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fb88` | `0x8003fcbc` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fcbc` | `0x8003fd64` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003fd64` | `0x8003fe5c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003fe5c` | `0x8003fef4` | 152 | `h_LT` | UNCONVERTED |
| `0x8003fef4` | `0x8003ff8c` | 152 | `h_GT` | UNCONVERTED |
| `0x8003ff8c` | `0x80040020` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040020` | `0x800400b4` | 148 | `h_SGT` | UNCONVERTED |
| `0x800400b4` | `0x80040138` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040138` | `0x80040198` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040198` | `0x8004020c` | 116 | `h_AND` | UNCONVERTED |
| `0x8004020c` | `0x80040280` | 116 | `h_OR` | UNCONVERTED |
| `0x80040280` | `0x800402f4` | 116 | `h_XOR` | UNCONVERTED |
| `0x800402f4` | `0x80040354` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040354` | `0x80040440` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040440` | `0x800405e0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800405e0` | `0x80040780` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040780` | `0x80040934` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040934` | `0x80040a34` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040a34` | `0x80040a68` | 52 | `h_POP` | UNCONVERTED |
| `0x80040a68` | `0x80040de4` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80040de4` | `0x800410f4` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x800410f4` | `0x8004122c` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x8004122c` | `0x80041270` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041270` | `0x800412b4` | 68 | `h_GAS` | UNCONVERTED |
| `0x800412b4` | `0x80041304` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041304` | `0x80041354` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041354` | `0x800413a4` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800413a4` | `0x800413f4` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x800413f4` | `0x80041444` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041444` | `0x80041494` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041494` | `0x800414e4` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800414e4` | `0x80041534` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041534` | `0x80041584` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041584` | `0x800415d4` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800415d4` | `0x80041624` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041624` | `0x80041674` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041674` | `0x800416c4` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x800416c4` | `0x80041714` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041714` | `0x80041764` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041764` | `0x800417fc` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800417fc` | `0x800418e8` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800418e8` | `0x8004192c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004192c` | `0x80041b48` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041b48` | `0x80041d30` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041d30` | `0x80041d74` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041d74` | `0x80041f58` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80041f58` | `0x80041f60` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80041f60` | `0x80042020` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042020` | `0x80042114` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042114` | `0x80042158` | 68 | `h_PC` | UNCONVERTED |
| `0x80042158` | `0x800423e0` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800423e0` | `0x800426d4` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800426d4` | `0x800429e8` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800429e8` | `0x80042d1c` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042d1c` | `0x80043070` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043070` | `0x800433e4` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800433e4` | `0x8004368c` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x8004368c` | `0x80043994` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043994` | `0x80044000` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044000` | `0x800445c0` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800445c0` | `0x80044b40` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044b40` | `0x800453cc` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800453cc` | `0x800454b8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800454b8` | `0x80045588` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045588` | `0x80045820` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80045820` | `0x800461b0` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x800461b0` | `0x8004678c` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x8004678c` | `0x800467a8` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800467a8` | `0x80047ccc` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047ccc` | `0x80047d18` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047d18` | `0x80047ed4` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047ed4` | `0x80048c9c` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048c9c` | `0x8004aed8` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004aed8` | `0x8004bfe0` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004bfe0` | `0x8004cc40` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004cc40` | `0x8004da48` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004da48` | `0x8004e6a8` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e6a8` | `0x8004ef60` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ef60` | `0x8004f854` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004f854` | `0x8004fdf0` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fdf0` | `0x8005049c` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x8005049c` | `0x800504bc` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800504bc` | `0x80050b68` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050b68` | `0x80050b88` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050b88` | `0x800514b8` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800514b8` | `0x80051804` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051804` | `0x80051974` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051974` | `0x80051978` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051978` | `0x80051a00` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051a00` | `0x80051bf4` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051bf4` | `0x80051c24` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051c24` | `0x80051c38` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051c38` | `0x80051c48` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051c48` | `0x80051c78` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051c78` | `0x80051e6c` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80051e6c` | `0x80051e9c` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80051e9c` | `0x80051eb0` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80051eb0` | `0x80051ec0` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80051ec0` | `0x80051ef0` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80051ef0` | `0x80051f14` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80051f14` | `0x80051f44` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80051f44` | `0x80052138` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052138` | `0x80052168` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052168` | `0x8005217c` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x8005217c` | `0x8005218c` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x8005218c` | `0x800521bc` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800521bc` | `0x800523b0` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800523b0` | `0x800523e0` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800523e0` | `0x800523f4` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800523f4` | `0x80052404` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052404` | `0x80052434` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052434` | `0x80052628` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052628` | `0x80052658` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052658` | `0x8005266c` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x8005266c` | `0x8005267c` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x8005267c` | `0x800526ac` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800526ac` | `0x800526ac` | 0 | `.exit_label` | UNCONVERTED |
| `0x800526ac` | `0x800526c8` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052700` | `0x8005271c` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x8005271c` | `0x80052738` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x80052738` | `0x80052854` | 284 | `stage_system_call` | UNCONVERTED |
| `0x80052854` | `0x80052a88` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80052a88` | `0x80052e90` | 1032 | `process_block_start_system_transactions` | UNCONVERTED |
| `0x80052e90` | `0x80052f90` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x80052f90` | `0x800530c0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800530c0` | `0x8005311c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x8005311c` | `0x8005313c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005313c` | `0x80053278` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053448` | `0x80053454` | 12 | `requests_hash_verify` | TAIL |
