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
not linked** (42 of 384 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x800533fc), 340988 bytes (`RegionMap.textSizeBytes = 0x533fc`)

- symbols in `.text`: 905 (342 converted, 563 unconverted)
- covered by converted `_prog`s: 84340 bytes (24.73%)
- NOT covered: 256648 bytes (75.27%), 564 ranges

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
| `0x80015924` | `0x80018420` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80018420` | `0x8001916c` | 3404 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x8001916c` | `0x80019388` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019670` | `0x80019704` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019efc` | `0x8001a154` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a154` | `0x8001a3cc` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a3cc` | `0x8001a660` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a89c` | `0x8001aa3c` | 416 | `bal_gas_valid_from_builder` | UNCONVERTED |
| `0x8001ac50` | `0x8001af08` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b2d0` | `0x8001b444` | 372 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b444` | `0x8001b5e4` | 416 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b5e4` | `0x8001c0c0` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c3c8` | `0x8001c410` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c544` | `0x8001c90c` | 968 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001c90c` | `0x8001c99c` | 144 | `stage_runtime_payload_witness_context` | UNCONVERTED |
| `0x8001c99c` | `0x8001cb84` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001cb84` | `0x8001cbe0` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001cbe0` | `0x8001ccac` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001ccac` | `0x8001cd80` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cd80` | `0x8001dca8` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e57c` | `0x8001e690` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e690` | `0x8001e998` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f130` | `0x8001f284` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8001f64c` | `0x8001f68c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f68c` | `0x8001f8ec` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x8001f8ec` | `0x8001fa34` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001fa34` | `0x8001fa64` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001fa64` | `0x8001fbf4` | 400 | `storage_read_record` | UNCONVERTED |
| `0x8001fbf4` | `0x8001fd70` | 380 | `storage_read_record_block` | UNCONVERTED |
| `0x8001fd70` | `0x8001ffb4` | 580 | `storage_write_record` | UNCONVERTED |
| `0x8001ffb4` | `0x80020144` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80020144` | `0x800202e8` | 420 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x800202e8` | `0x800203a8` | 192 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x800203a8` | `0x800203d0` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x800203d0` | `0x800204cc` | 252 | `storage_writes_undo_push` | UNCONVERTED |
| `0x800204cc` | `0x80020610` | 324 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80020610` | `0x80020850` | 576 | `account_write_record` | UNCONVERTED |
| `0x80020850` | `0x80020990` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x80020990` | `0x80020a58` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x80020a58` | `0x80020b08` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x80020b08` | `0x80020bb8` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80020bb8` | `0x80020d28` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x80020d28` | `0x80020e34` | 268 | `account_writes_auth_block` | UNCONVERTED |
| `0x80020e34` | `0x80020ed8` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x80020ed8` | `0x80021064` | 396 | `account_writes_lookup_current` | UNCONVERTED |
| `0x80021064` | `0x80021338` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x80021338` | `0x80021454` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021454` | `0x80021618` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021618` | `0x800218a8` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800218a8` | `0x800218f8` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x800218f8` | `0x800219ec` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x800219ec` | `0x80021ef0` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x80021ef0` | `0x80021f7c` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x80021f7c` | `0x8002209c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x8002209c` | `0x800221a0` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x800221a0` | `0x8002235c` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x8002235c` | `0x800227b8` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x800227b8` | `0x80022a60` | 680 | `bal_map_final_value_matches` | UNCONVERTED |
| `0x80022a60` | `0x80022b50` | 240 | `bal_map_builder_consistent` | UNCONVERTED |
| `0x80022d9c` | `0x80022db8` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022db8` | `0x80022e2c` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022e2c` | `0x80022e7c` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022e7c` | `0x80022ea8` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022ea8` | `0x80022f88` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022f88` | `0x80023008` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023008` | `0x80023038` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023038` | `0x80023178` | 320 | `bal_rlp_emit_bytes` | UNCONVERTED |
| `0x80023178` | `0x8002323c` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x8002323c` | `0x80023290` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023290` | `0x800232c0` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800232c0` | `0x80023300` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023300` | `0x80023338` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023338` | `0x80023378` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023378` | `0x80023434` | 188 | `bal_serializer_slot_written` | UNCONVERTED |
| `0x80023434` | `0x800234d8` | 164 | `bal_serializer_slot_seen_before` | UNCONVERTED |
| `0x800234d8` | `0x800234f0` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800234f0` | `0x800235cc` | 220 | `bal_serializer_measure_reads` | UNCONVERTED |
| `0x800235cc` | `0x800235fc` | 48 | `bal_serializer_slot_to_le` | UNCONVERTED |
| `0x800235fc` | `0x8002362c` | 48 | `bal_serializer_balance_to_le` | UNCONVERTED |
| `0x8002362c` | `0x80023738` | 268 | `bal_serializer_measure_slot` | UNCONVERTED |
| `0x80023738` | `0x80023818` | 224 | `bal_serializer_measure_storage` | UNCONVERTED |
| `0x80023818` | `0x800238f4` | 220 | `bal_serializer_measure_balance` | UNCONVERTED |
| `0x800238f4` | `0x800239dc` | 232 | `bal_serializer_measure_nonce` | UNCONVERTED |
| `0x800239dc` | `0x80023acc` | 240 | `bal_serializer_measure_code` | UNCONVERTED |
| `0x80023acc` | `0x80023bb0` | 228 | `bal_serializer_measure_account` | UNCONVERTED |
| `0x80023bb0` | `0x80023d90` | 480 | `bal_serializer_emit_storage` | UNCONVERTED |
| `0x80023d90` | `0x80023e5c` | 204 | `bal_serializer_emit_reads` | UNCONVERTED |
| `0x80023e5c` | `0x80023fa0` | 324 | `bal_serializer_emit_balance` | UNCONVERTED |
| `0x80023fa0` | `0x80024118` | 376 | `bal_serializer_emit_nonce` | UNCONVERTED |
| `0x80024118` | `0x8002424c` | 308 | `bal_serializer_emit_code` | UNCONVERTED |
| `0x8002424c` | `0x80024378` | 300 | `bal_serializer_emit_account` | UNCONVERTED |
| `0x80024378` | `0x80024408` | 144 | `bal_serializer_measure_outer` | UNCONVERTED |
| `0x80024408` | `0x800244b0` | 168 | `bal_serializer_emit_outer` | UNCONVERTED |
| `0x800244b0` | `0x800246ac` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800246ac` | `0x80024744` | 152 | `bal_serializer_verify` | UNCONVERTED |
| `0x80024744` | `0x80024850` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024850` | `0x800248b4` | 100 | `bal_builder_incorporate_touched_accounts` | UNCONVERTED |
| `0x800248b4` | `0x80024a7c` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024a7c` | `0x80024d64` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024d64` | `0x80024e4c` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024e4c` | `0x80024f28` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024f28` | `0x80025000` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025000` | `0x80025124` | 292 | `account_read_record` | UNCONVERTED |
| `0x80025124` | `0x80025178` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x80025178` | `0x800252d8` | 352 | `code_read_record` | UNCONVERTED |
| `0x800252d8` | `0x80025384` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x80025384` | `0x800254a8` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800254a8` | `0x800255a0` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800255a0` | `0x800255c8` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x800255c8` | `0x800256f0` | 296 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80025b44` | `0x80025d74` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80025d74` | `0x80025d84` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025f68` | `0x80026180` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026180` | `0x80026374` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026708` | `0x80026d8c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027b0c` | `0x80027c44` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80027c44` | `0x80027ca8` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x80027ca8` | `0x800281c4` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028224` | `0x800282c4` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x8002897c` | `0x80028b0c` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x80028b0c` | `0x80028e88` | 892 | `eip7702_authority_asof` | UNCONVERTED |
| `0x80028e88` | `0x8002967c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002967c` | `0x800299b4` | 824 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x800299b4` | `0x80029aa4` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x80029d10` | `0x80029fac` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029fac` | `0x80029fe4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002a3ac` | `0x8002a498` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002bbdc` | `0x8002c0cc` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c0cc` | `0x8002cb18` | 2636 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cb18` | `0x8002d0e8` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d0e8` | `0x8002eaa8` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002eaa8` | `0x8002eacc` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002eacc` | `0x8002eae8` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002eae8` | `0x8002edac` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002edac` | `0x8002edbc` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002edbc` | `0x8002edf0` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002edf0` | `0x8002ee08` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002ee08` | `0x8002ee18` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002ee18` | `0x8002ee4c` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002ee4c` | `0x8002ee54` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002ee54` | `0x8002ef00` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ef00` | `0x8002ef0c` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ef0c` | `0x8002ef34` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ef34` | `0x8002ef74` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ef74` | `0x8002efa4` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002efa4` | `0x8002efa4` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002efa4` | `0x8002efbc` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002efbc` | `0x8002efc4` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002efc4` | `0x8002efd0` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002efd0` | `0x8002efe8` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002efe8` | `0x8002f000` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f000` | `0x8002f014` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f014` | `0x8002f034` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f034` | `0x8002f048` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f048` | `0x8002f074` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f074` | `0x8002f0bc` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f0bc` | `0x8002f19c` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f19c` | `0x8002f24c` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f24c` | `0x8002f26c` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f26c` | `0x8002f2e0` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f2e0` | `0x8002f2f0` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f2f0` | `0x8002f2fc` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f2fc` | `0x8002f3e0` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f3e0` | `0x8002f408` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f408` | `0x8002f41c` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f41c` | `0x8002f41c` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f41c` | `0x8002f41c` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f41c` | `0x8002f43c` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f43c` | `0x8002f46c` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f46c` | `0x8002f490` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f490` | `0x8002f4b0` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f4b0` | `0x8002f4b4` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f4b4` | `0x8002f540` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f540` | `0x8002f550` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f550` | `0x8002f560` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f560` | `0x8002f690` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f690` | `0x8002f690` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f690` | `0x8002f82c` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002f82c` | `0x8002f88c` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8002f88c` | `0x8002f9e4` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x80030644` | `0x8003066c` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x8003066c` | `0x8003087c` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800308dc` | `0x8003097c` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x8003097c` | `0x80030a28` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030a28` | `0x80030aac` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030aac` | `0x80030b2c` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030b2c` | `0x80030be4` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030be4` | `0x80030c58` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030c58` | `0x80030e1c` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80030e1c` | `0x80030e8c` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80030e8c` | `0x80030f04` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80030f04` | `0x800310b4` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800310b4` | `0x80031130` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031130` | `0x80031180` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031180` | `0x800311d0` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800311d0` | `0x80031200` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031200` | `0x80031244` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031244` | `0x80031288` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031288` | `0x80031338` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031338` | `0x80031494` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031494` | `0x80031790` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031790` | `0x8003196c` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8003196c` | `0x80031a18` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031a18` | `0x80031b90` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031b90` | `0x80031d5c` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031d5c` | `0x80031e90` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80031f80` | `0x8003205c` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8003205c` | `0x800321ac` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800321ac` | `0x80032388` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032538` | `0x80032724` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032724` | `0x80032778` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032778` | `0x800327c0` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800327c0` | `0x80032894` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032894` | `0x80032974` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032974` | `0x80032b2c` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80032b2c` | `0x80032c48` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x800332c8` | `0x800333a4` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x800333a4` | `0x80033514` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80033544` | `0x800335c0` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800335c0` | `0x800336ac` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033d10` | `0x80033d80` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033d80` | `0x80033de0` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x8003402c` | `0x800341bc` | 400 | `bnq_mul` | UNCONVERTED |
| `0x800341bc` | `0x80034210` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800343d8` | `0x80034644` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034644` | `0x80034984` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034984` | `0x80034c34` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034c34` | `0x80034f68` | 820 | `bng2_double` | UNCONVERTED |
| `0x80034f68` | `0x800352f0` | 904 | `bng2_add` | UNCONVERTED |
| `0x800352f0` | `0x80035410` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035430` | `0x80035860` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035860` | `0x80035ca4` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035cf8` | `0x80035ea4` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80035fc4` | `0x8003618c` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80036318` | `0x800364dc` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036c6c` | `0x80036f44` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037318` | `0x80037428` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80037428` | `0x8003757c` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x8003757c` | `0x800376b4` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037830` | `0x800378c0` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800378c0` | `0x80037990` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037990` | `0x80037b68` | 472 | `blq_mul` | UNCONVERTED |
| `0x80037b68` | `0x80037bc4` | 92 | `blq_sub` | UNCONVERTED |
| `0x80037db4` | `0x80038020` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038020` | `0x80038340` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038340` | `0x800385f0` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800385f0` | `0x800387cc` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800387cc` | `0x80038b14` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038c60` | `0x8003a4c4` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a4c4` | `0x8003b700` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003b780` | `0x8003b824` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003b824` | `0x8003b940` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003b950` | `0x8003b980` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003b980` | `0x8003bf1c` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003bf1c` | `0x8003c22c` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c22c` | `0x8003c234` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c234` | `0x8003c238` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c238` | `0x8003c41c` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c4ac` | `0x8003c514` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003c514` | `0x8003c75c` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c75c` | `0x8003cdc0` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003cdc0` | `0x8003cedc` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003cedc` | `0x8003d0f4` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d0f4` | `0x8003d134` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d134` | `0x8003d17c` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d17c` | `0x8003d1cc` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d1cc` | `0x8003d224` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d224` | `0x8003d284` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d284` | `0x8003d2ec` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d2ec` | `0x8003d35c` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d35c` | `0x8003d3d4` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d3d4` | `0x8003d454` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d454` | `0x8003d4dc` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d4dc` | `0x8003d56c` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d56c` | `0x8003d604` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d604` | `0x8003d6a4` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d6a4` | `0x8003d74c` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d74c` | `0x8003d7fc` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003d7fc` | `0x8003d8b4` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003d8b4` | `0x8003d974` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003d974` | `0x8003da3c` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003da3c` | `0x8003db0c` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003db0c` | `0x8003dbe4` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003dbe4` | `0x8003dcc4` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003dcc4` | `0x8003ddac` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ddac` | `0x8003de9c` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003de9c` | `0x8003df94` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003df94` | `0x8003e094` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e094` | `0x8003e19c` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e19c` | `0x8003e2ac` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e2ac` | `0x8003e3c4` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e3c4` | `0x8003e4e4` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e4e4` | `0x8003e60c` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e60c` | `0x8003e73c` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e73c` | `0x8003e874` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003e874` | `0x8003e9b4` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003e9b4` | `0x8003ea2c` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ea2c` | `0x8003eaa4` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003eaa4` | `0x8003eb1c` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003eb1c` | `0x8003eb94` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003eb94` | `0x8003ec0c` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ec0c` | `0x8003ec84` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003ec84` | `0x8003ecfc` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ecfc` | `0x8003ed74` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003ed74` | `0x8003edec` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003edec` | `0x8003ee64` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003ee64` | `0x8003eedc` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003eedc` | `0x8003ef54` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ef54` | `0x8003efcc` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003efcc` | `0x8003f044` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f044` | `0x8003f0bc` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f0bc` | `0x8003f134` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f134` | `0x8003f1a4` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f1a4` | `0x8003f214` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f214` | `0x8003f284` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f284` | `0x8003f2f4` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f2f4` | `0x8003f364` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f364` | `0x8003f3d4` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f3d4` | `0x8003f444` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f444` | `0x8003f4b4` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f4b4` | `0x8003f524` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f524` | `0x8003f594` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f594` | `0x8003f604` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f604` | `0x8003f674` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f674` | `0x8003f6e4` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f6e4` | `0x8003f754` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f754` | `0x8003f7c4` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003f7c4` | `0x8003f834` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003f834` | `0x8003f84c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003f84c` | `0x8003f860` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003f860` | `0x8003f8ec` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003f8ec` | `0x8003f904` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003f904` | `0x8003f918` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003f918` | `0x8003f9a0` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003f9a0` | `0x8003f9b8` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003f9b8` | `0x8003f9cc` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003f9cc` | `0x8003f9ec` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003f9ec` | `0x8003f9f4` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003f9f4` | `0x8003fa00` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003fa00` | `0x8003fa04` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003fa04` | `0x8003fa88` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fa88` | `0x8003fb30` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fb30` | `0x8003fc64` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fc64` | `0x8003fd0c` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003fd0c` | `0x8003fe04` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003fe04` | `0x8003fe9c` | 152 | `h_LT` | UNCONVERTED |
| `0x8003fe9c` | `0x8003ff34` | 152 | `h_GT` | UNCONVERTED |
| `0x8003ff34` | `0x8003ffc8` | 148 | `h_SLT` | UNCONVERTED |
| `0x8003ffc8` | `0x8004005c` | 148 | `h_SGT` | UNCONVERTED |
| `0x8004005c` | `0x800400e0` | 132 | `h_EQ` | UNCONVERTED |
| `0x800400e0` | `0x80040140` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040140` | `0x800401b4` | 116 | `h_AND` | UNCONVERTED |
| `0x800401b4` | `0x80040228` | 116 | `h_OR` | UNCONVERTED |
| `0x80040228` | `0x8004029c` | 116 | `h_XOR` | UNCONVERTED |
| `0x8004029c` | `0x800402fc` | 96 | `h_NOT` | UNCONVERTED |
| `0x800402fc` | `0x800403e8` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800403e8` | `0x80040588` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040588` | `0x80040728` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040728` | `0x800408dc` | 436 | `h_SAR` | UNCONVERTED |
| `0x800408dc` | `0x800409dc` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800409dc` | `0x80040a10` | 52 | `h_POP` | UNCONVERTED |
| `0x80040a10` | `0x80040d8c` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80040d8c` | `0x8004109c` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x8004109c` | `0x800411d4` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x800411d4` | `0x80041218` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041218` | `0x8004125c` | 68 | `h_GAS` | UNCONVERTED |
| `0x8004125c` | `0x800412ac` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x800412ac` | `0x800412fc` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800412fc` | `0x8004134c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x8004134c` | `0x8004139c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8004139c` | `0x800413ec` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800413ec` | `0x8004143c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x8004143c` | `0x8004148c` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x8004148c` | `0x800414dc` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800414dc` | `0x8004152c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x8004152c` | `0x8004157c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004157c` | `0x800415cc` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800415cc` | `0x8004161c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x8004161c` | `0x8004166c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004166c` | `0x800416bc` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800416bc` | `0x8004170c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x8004170c` | `0x800417a4` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800417a4` | `0x80041890` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041890` | `0x800418d4` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800418d4` | `0x80041af0` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041af0` | `0x80041cd8` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041cd8` | `0x80041d1c` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041d1c` | `0x80041f00` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80041f00` | `0x80041f08` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80041f08` | `0x80041fc8` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80041fc8` | `0x800420bc` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x800420bc` | `0x80042100` | 68 | `h_PC` | UNCONVERTED |
| `0x80042100` | `0x80042388` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042388` | `0x8004267c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004267c` | `0x80042990` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042990` | `0x80042cc4` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042cc4` | `0x80043018` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043018` | `0x8004338c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x8004338c` | `0x80043634` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043634` | `0x8004393c` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8004393c` | `0x80043fa8` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80043fa8` | `0x80044568` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044568` | `0x80044ae8` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044ae8` | `0x80045374` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045374` | `0x80045460` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045460` | `0x80045530` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045530` | `0x800457c8` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x800457c8` | `0x80046158` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046158` | `0x80046734` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046734` | `0x80046750` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046750` | `0x80047c74` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047c74` | `0x80047cc0` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047cc0` | `0x80047e7c` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047e7c` | `0x80048c44` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048c44` | `0x8004ae80` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004ae80` | `0x8004bf88` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004bf88` | `0x8004cbe8` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004cbe8` | `0x8004d9f0` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004d9f0` | `0x8004e650` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e650` | `0x8004ef08` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ef08` | `0x8004f7fc` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004f7fc` | `0x8004fd98` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fd98` | `0x80050444` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050444` | `0x80050464` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050464` | `0x80050b10` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050b10` | `0x80050b30` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050b30` | `0x80051460` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051460` | `0x800517ac` | 844 | `h_EXP` | UNCONVERTED |
| `0x800517ac` | `0x8005191c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005191c` | `0x80051920` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051920` | `0x800519a8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800519a8` | `0x80051b9c` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051b9c` | `0x80051bcc` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051bcc` | `0x80051be0` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051be0` | `0x80051bf0` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051bf0` | `0x80051c20` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051c20` | `0x80051e14` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80051e14` | `0x80051e44` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80051e44` | `0x80051e58` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80051e58` | `0x80051e68` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80051e68` | `0x80051e98` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80051e98` | `0x80051ebc` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80051ebc` | `0x80051eec` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80051eec` | `0x800520e0` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800520e0` | `0x80052110` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052110` | `0x80052124` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052124` | `0x80052134` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052134` | `0x80052164` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052164` | `0x80052358` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052358` | `0x80052388` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052388` | `0x8005239c` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x8005239c` | `0x800523ac` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800523ac` | `0x800523dc` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800523dc` | `0x800525d0` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800525d0` | `0x80052600` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052600` | `0x80052614` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052614` | `0x80052624` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052624` | `0x80052654` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052654` | `0x80052654` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052654` | `0x80052670` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800526a8` | `0x800526c4` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x800526c4` | `0x800526e0` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x800526e0` | `0x800527fc` | 284 | `stage_system_call` | UNCONVERTED |
| `0x800527fc` | `0x80052a30` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80052a30` | `0x80052e38` | 1032 | `process_block_start_system_transactions` | UNCONVERTED |
| `0x80052e38` | `0x80052f38` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x80052f38` | `0x80053068` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053068` | `0x800530c4` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800530c4` | `0x800530e4` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800530e4` | `0x80053220` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x800533f0` | `0x800533fc` | 12 | `requests_hash_verify` | TAIL |
