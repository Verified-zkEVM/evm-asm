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
not linked** (41 of 371 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053300), 340736 bytes (`RegionMap.textSizeBytes = 0x53300`)

- symbols in `.text`: 902 (330 converted, 572 unconverted)
- covered by converted `_prog`s: 80608 bytes (23.66%)
- NOT covered: 260128 bytes (76.34%), 573 ranges

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
| `0x80005328` | `0x8000551c` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x800097dc` | `0x800099a0` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x800099a0` | `0x80009a0c` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a0cc` | `0x8000a2c8` | 508 | `mpt_indexed_stream_leaf_hash` | UNCONVERTED |
| `0x8000a2c8` | `0x8000a4c8` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a4c8` | `0x8000a608` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a608` | `0x8000a8c4` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a8c4` | `0x8000a9b4` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a9b4` | `0x8000ab24` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000ba58` | `0x8000bfe8` | 1424 | `block_header_ssz_to_rlp` | UNCONVERTED |
| `0x8000ddd4` | `0x8000f0f0` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f520` | `0x8000f700` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f700` | `0x8000f7e4` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f7e4` | `0x8000f8c0` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f8c0` | `0x8000f954` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f954` | `0x8000fa10` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fa10` | `0x8000fac0` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fac0` | `0x8000fba4` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000fba4` | `0x8000fbe0` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000fbe0` | `0x8000fd10` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000fd10` | `0x8000fe34` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000fe34` | `0x8000fee4` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000fee4` | `0x80010060` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010060` | `0x80010138` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010138` | `0x800102c8` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x800102c8` | `0x80010464` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010464` | `0x80010514` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010514` | `0x8001057c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8001057c` | `0x80010618` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010618` | `0x80010c4c` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010c4c` | `0x80010f34` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010f34` | `0x8001128c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001128c` | `0x80011768` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011768` | `0x80011a0c` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011a0c` | `0x80011b28` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011b28` | `0x80011de0` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011de0` | `0x80012000` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012000` | `0x80012398` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012398` | `0x800124ac` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x800124ac` | `0x800124cc` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x800124cc` | `0x80012754` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012754` | `0x80012838` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012838` | `0x800128e0` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800128e0` | `0x80013014` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013014` | `0x8001364c` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001364c` | `0x8001381c` | 464 | `chain_config_valid` | UNCONVERTED |
| `0x8001381c` | `0x80013988` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80013988` | `0x8001399c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x8001399c` | `0x800139a8` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800139a8` | `0x800139f8` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800139f8` | `0x80013a18` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013a18` | `0x80013a7c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013a7c` | `0x80013d24` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013d24` | `0x80013f78` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80013f78` | `0x8001412c` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x8001412c` | `0x8001453c` | 1040 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80014d2c` | `0x80014f24` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015244` | `0x80015474` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015570` | `0x80015864` | 756 | `simple_transfer_intrinsic_gas` | UNCONVERTED |
| `0x80015864` | `0x8001838c` | 11048 | `block_verdict` | UNCONVERTED |
| `0x8001838c` | `0x80019104` | 3448 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019104` | `0x80019320` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019e00` | `0x8001a058` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a058` | `0x8001a2d0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a2d0` | `0x8001a564` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a7a0` | `0x8001a940` | 416 | `bal_gas_valid_from_builder` | UNCONVERTED |
| `0x8001ab54` | `0x8001ae0c` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b1d4` | `0x8001b348` | 372 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b348` | `0x8001b4e8` | 416 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b4e8` | `0x8001bfc4` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c2cc` | `0x8001c314` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c448` | `0x8001c810` | 968 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001c810` | `0x8001c8a0` | 144 | `stage_runtime_payload_witness_context` | UNCONVERTED |
| `0x8001c8a0` | `0x8001ca88` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001ca88` | `0x8001cae4` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001cae4` | `0x8001cbb0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001cbb0` | `0x8001cc84` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cc84` | `0x8001dbac` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e480` | `0x8001e594` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e594` | `0x8001e89c` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f034` | `0x8001f188` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8001f550` | `0x8001f590` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f590` | `0x8001f7f0` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x8001f7f0` | `0x8001f938` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001f938` | `0x8001f968` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001f968` | `0x8001faf8` | 400 | `storage_read_record` | UNCONVERTED |
| `0x8001faf8` | `0x8001fc74` | 380 | `storage_read_record_block` | UNCONVERTED |
| `0x8001fc74` | `0x8001feb8` | 580 | `storage_write_record` | UNCONVERTED |
| `0x8001feb8` | `0x80020048` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80020048` | `0x800201ec` | 420 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x800201ec` | `0x800202ac` | 192 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x800202ac` | `0x800202d4` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x800202d4` | `0x800203d0` | 252 | `storage_writes_undo_push` | UNCONVERTED |
| `0x800203d0` | `0x80020514` | 324 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80020514` | `0x80020754` | 576 | `account_write_record` | UNCONVERTED |
| `0x80020754` | `0x80020894` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x80020894` | `0x8002095c` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x8002095c` | `0x80020a0c` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x80020a0c` | `0x80020abc` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80020abc` | `0x80020c2c` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x80020c2c` | `0x80020d38` | 268 | `account_writes_auth_block` | UNCONVERTED |
| `0x80020d38` | `0x80020ddc` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x80020ddc` | `0x80020f68` | 396 | `account_writes_lookup_current` | UNCONVERTED |
| `0x80020f68` | `0x8002123c` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x8002123c` | `0x80021358` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021358` | `0x8002151c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x8002151c` | `0x800217ac` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800217ac` | `0x800217fc` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x800217fc` | `0x800218f0` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x800218f0` | `0x80021df4` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x80021df4` | `0x80021e80` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x80021e80` | `0x80021fa0` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80021fa0` | `0x800220a4` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x800220a4` | `0x80022260` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x80022260` | `0x800226bc` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x800226bc` | `0x80022964` | 680 | `bal_map_final_value_matches` | UNCONVERTED |
| `0x80022964` | `0x80022a54` | 240 | `bal_map_builder_consistent` | UNCONVERTED |
| `0x80022ca0` | `0x80022cbc` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022cbc` | `0x80022d30` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022d30` | `0x80022d80` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022d80` | `0x80022dac` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022dac` | `0x80022e8c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022e8c` | `0x80022f0c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80022f0c` | `0x80022f3c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80022f3c` | `0x8002307c` | 320 | `bal_rlp_emit_bytes` | UNCONVERTED |
| `0x8002307c` | `0x80023140` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023140` | `0x80023194` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023194` | `0x800231c4` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800231c4` | `0x80023204` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023204` | `0x8002323c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002323c` | `0x8002327c` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x8002327c` | `0x80023338` | 188 | `bal_serializer_slot_written` | UNCONVERTED |
| `0x80023338` | `0x800233dc` | 164 | `bal_serializer_slot_seen_before` | UNCONVERTED |
| `0x800233dc` | `0x800233f4` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800233f4` | `0x800234d0` | 220 | `bal_serializer_measure_reads` | UNCONVERTED |
| `0x800234d0` | `0x80023500` | 48 | `bal_serializer_slot_to_le` | UNCONVERTED |
| `0x80023500` | `0x80023530` | 48 | `bal_serializer_balance_to_le` | UNCONVERTED |
| `0x80023530` | `0x8002363c` | 268 | `bal_serializer_measure_slot` | UNCONVERTED |
| `0x8002363c` | `0x8002371c` | 224 | `bal_serializer_measure_storage` | UNCONVERTED |
| `0x8002371c` | `0x800237f8` | 220 | `bal_serializer_measure_balance` | UNCONVERTED |
| `0x800237f8` | `0x800238e0` | 232 | `bal_serializer_measure_nonce` | UNCONVERTED |
| `0x800238e0` | `0x800239d0` | 240 | `bal_serializer_measure_code` | UNCONVERTED |
| `0x800239d0` | `0x80023ab4` | 228 | `bal_serializer_measure_account` | UNCONVERTED |
| `0x80023ab4` | `0x80023c94` | 480 | `bal_serializer_emit_storage` | UNCONVERTED |
| `0x80023c94` | `0x80023d60` | 204 | `bal_serializer_emit_reads` | UNCONVERTED |
| `0x80023d60` | `0x80023ea4` | 324 | `bal_serializer_emit_balance` | UNCONVERTED |
| `0x80023ea4` | `0x8002401c` | 376 | `bal_serializer_emit_nonce` | UNCONVERTED |
| `0x8002401c` | `0x80024150` | 308 | `bal_serializer_emit_code` | UNCONVERTED |
| `0x80024150` | `0x8002427c` | 300 | `bal_serializer_emit_account` | UNCONVERTED |
| `0x8002427c` | `0x8002430c` | 144 | `bal_serializer_measure_outer` | UNCONVERTED |
| `0x8002430c` | `0x800243b4` | 168 | `bal_serializer_emit_outer` | UNCONVERTED |
| `0x800243b4` | `0x800245b0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800245b0` | `0x80024648` | 152 | `bal_serializer_verify` | UNCONVERTED |
| `0x80024648` | `0x80024754` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024754` | `0x800247b8` | 100 | `bal_builder_incorporate_touched_accounts` | UNCONVERTED |
| `0x800247b8` | `0x80024980` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024980` | `0x80024c68` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024c68` | `0x80024d50` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024d50` | `0x80024e2c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024e2c` | `0x80024f04` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80024f04` | `0x80025028` | 292 | `account_read_record` | UNCONVERTED |
| `0x80025028` | `0x8002507c` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x8002507c` | `0x800251dc` | 352 | `code_read_record` | UNCONVERTED |
| `0x800251dc` | `0x80025288` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x80025288` | `0x800253ac` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800253ac` | `0x800254a4` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800254a4` | `0x800254cc` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x800254cc` | `0x800255f4` | 296 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80025a48` | `0x80025c78` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80025c78` | `0x80025c88` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025e6c` | `0x80026084` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026084` | `0x80026278` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x8002660c` | `0x80026c90` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027a10` | `0x80027b48` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80027b48` | `0x80027bac` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x80027bac` | `0x800280c8` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028128` | `0x800281c8` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028570` | `0x800286c8` | 344 | `eip7702_authorization_extract_signature` | UNCONVERTED |
| `0x80028880` | `0x80028a10` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x80028a10` | `0x80028d8c` | 892 | `eip7702_authority_asof` | UNCONVERTED |
| `0x80028d8c` | `0x80029580` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029580` | `0x800298b8` | 824 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x800298b8` | `0x800299a8` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x80029c14` | `0x80029eb0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029eb0` | `0x80029ee8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002a2b0` | `0x8002a39c` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002a4ec` | `0x8002a680` | 404 | `tx_legacy_extract_signature` | UNCONVERTED |
| `0x8002a680` | `0x8002a83c` | 444 | `tx_eip2930_extract_signature` | UNCONVERTED |
| `0x8002a83c` | `0x8002aa0c` | 464 | `tx_eip1559_extract_signature` | UNCONVERTED |
| `0x8002aa0c` | `0x8002ac04` | 504 | `tx_eip4844_extract_signature` | UNCONVERTED |
| `0x8002ac04` | `0x8002ade8` | 484 | `tx_eip7702_extract_signature` | UNCONVERTED |
| `0x8002bae0` | `0x8002bfd0` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002bfd0` | `0x8002ca1c` | 2636 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002ca1c` | `0x8002cfec` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002cfec` | `0x8002e9ac` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002e9ac` | `0x8002e9d0` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002e9d0` | `0x8002e9ec` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002e9ec` | `0x8002ecb0` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002ecb0` | `0x8002ecc0` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002ecc0` | `0x8002ecf4` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002ecf4` | `0x8002ed0c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002ed0c` | `0x8002ed1c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002ed1c` | `0x8002ed50` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002ed50` | `0x8002ed58` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002ed58` | `0x8002ee04` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ee04` | `0x8002ee10` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ee10` | `0x8002ee38` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ee38` | `0x8002ee78` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ee78` | `0x8002eea8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002eea8` | `0x8002eea8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002eea8` | `0x8002eec0` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002eec0` | `0x8002eec8` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002eec8` | `0x8002eed4` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002eed4` | `0x8002eeec` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002eeec` | `0x8002ef04` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002ef04` | `0x8002ef18` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002ef18` | `0x8002ef38` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002ef38` | `0x8002ef4c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002ef4c` | `0x8002ef78` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002ef78` | `0x8002efc0` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002efc0` | `0x8002f0a0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f0a0` | `0x8002f150` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f150` | `0x8002f170` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f170` | `0x8002f1e4` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f1e4` | `0x8002f1f4` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f1f4` | `0x8002f200` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f200` | `0x8002f2e4` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f2e4` | `0x8002f30c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f30c` | `0x8002f320` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f320` | `0x8002f320` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f320` | `0x8002f320` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f320` | `0x8002f340` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f340` | `0x8002f370` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f370` | `0x8002f394` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f394` | `0x8002f3b4` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f3b4` | `0x8002f3b8` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f3b8` | `0x8002f444` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f444` | `0x8002f454` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f454` | `0x8002f464` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f464` | `0x8002f594` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f594` | `0x8002f594` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f594` | `0x8002f730` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002f730` | `0x8002f790` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8002f790` | `0x8002f8e8` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x80030548` | `0x80030570` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030570` | `0x80030780` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800307e0` | `0x80030880` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x80030880` | `0x8003092c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x8003092c` | `0x800309b0` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800309b0` | `0x80030a30` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030a30` | `0x80030ae8` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030ae8` | `0x80030b5c` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030b5c` | `0x80030d20` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80030d20` | `0x80030d90` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80030d90` | `0x80030e08` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80030e08` | `0x80030fb8` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80030fb8` | `0x80031034` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031034` | `0x80031084` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031084` | `0x800310d4` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800310d4` | `0x80031104` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031104` | `0x80031148` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031148` | `0x8003118c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x8003118c` | `0x8003123c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8003123c` | `0x80031398` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031398` | `0x80031694` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031694` | `0x80031870` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031870` | `0x8003191c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x8003191c` | `0x80031a94` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031a94` | `0x80031c60` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031c60` | `0x80031d94` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80031e84` | `0x80031f60` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80031f60` | `0x800320b0` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800320b0` | `0x8003228c` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x8003243c` | `0x80032628` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032628` | `0x8003267c` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x8003267c` | `0x800326c4` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800326c4` | `0x80032798` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032798` | `0x80032878` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032878` | `0x80032a30` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80032a30` | `0x80032b4c` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x800331cc` | `0x800332a8` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x800332a8` | `0x80033418` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80033448` | `0x800334c4` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800334c4` | `0x800335b0` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033c14` | `0x80033c84` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033c84` | `0x80033ce4` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80033f30` | `0x800340c0` | 400 | `bnq_mul` | UNCONVERTED |
| `0x800340c0` | `0x80034114` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800342dc` | `0x80034548` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034548` | `0x80034888` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034888` | `0x80034b38` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034b38` | `0x80034e6c` | 820 | `bng2_double` | UNCONVERTED |
| `0x80034e6c` | `0x800351f4` | 904 | `bng2_add` | UNCONVERTED |
| `0x800351f4` | `0x80035314` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035334` | `0x80035764` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035764` | `0x80035ba8` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035bfc` | `0x80035da8` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80035ec8` | `0x80036090` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x8003621c` | `0x800363e0` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036b70` | `0x80036e48` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003721c` | `0x8003732c` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x8003732c` | `0x80037480` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80037480` | `0x800375b8` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037734` | `0x800377c4` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800377c4` | `0x80037894` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037894` | `0x80037a6c` | 472 | `blq_mul` | UNCONVERTED |
| `0x80037a6c` | `0x80037ac8` | 92 | `blq_sub` | UNCONVERTED |
| `0x80037cb8` | `0x80037f24` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80037f24` | `0x80038244` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038244` | `0x800384f4` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800384f4` | `0x800386d0` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800386d0` | `0x80038a18` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038b64` | `0x8003a3c8` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a3c8` | `0x8003b604` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003b684` | `0x8003b728` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003b728` | `0x8003b844` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003b854` | `0x8003b884` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003b884` | `0x8003be20` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003be20` | `0x8003c130` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c130` | `0x8003c138` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c138` | `0x8003c13c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c13c` | `0x8003c320` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c3b0` | `0x8003c418` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003c418` | `0x8003c660` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c660` | `0x8003ccc4` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ccc4` | `0x8003cde0` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003cde0` | `0x8003cff8` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003cff8` | `0x8003d038` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d038` | `0x8003d080` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d080` | `0x8003d0d0` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d0d0` | `0x8003d128` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d128` | `0x8003d188` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d188` | `0x8003d1f0` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d1f0` | `0x8003d260` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d260` | `0x8003d2d8` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d2d8` | `0x8003d358` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d358` | `0x8003d3e0` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d3e0` | `0x8003d470` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d470` | `0x8003d508` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d508` | `0x8003d5a8` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d5a8` | `0x8003d650` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d650` | `0x8003d700` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003d700` | `0x8003d7b8` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003d7b8` | `0x8003d878` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003d878` | `0x8003d940` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003d940` | `0x8003da10` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003da10` | `0x8003dae8` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003dae8` | `0x8003dbc8` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003dbc8` | `0x8003dcb0` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003dcb0` | `0x8003dda0` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003dda0` | `0x8003de98` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003de98` | `0x8003df98` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003df98` | `0x8003e0a0` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e0a0` | `0x8003e1b0` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e1b0` | `0x8003e2c8` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e2c8` | `0x8003e3e8` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e3e8` | `0x8003e510` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e510` | `0x8003e640` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e640` | `0x8003e778` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003e778` | `0x8003e8b8` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003e8b8` | `0x8003e930` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003e930` | `0x8003e9a8` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003e9a8` | `0x8003ea20` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003ea20` | `0x8003ea98` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ea98` | `0x8003eb10` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003eb10` | `0x8003eb88` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003eb88` | `0x8003ec00` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ec00` | `0x8003ec78` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003ec78` | `0x8003ecf0` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003ecf0` | `0x8003ed68` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003ed68` | `0x8003ede0` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ede0` | `0x8003ee58` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ee58` | `0x8003eed0` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003eed0` | `0x8003ef48` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003ef48` | `0x8003efc0` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003efc0` | `0x8003f038` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f038` | `0x8003f0a8` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f0a8` | `0x8003f118` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f118` | `0x8003f188` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f188` | `0x8003f1f8` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f1f8` | `0x8003f268` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f268` | `0x8003f2d8` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f2d8` | `0x8003f348` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f348` | `0x8003f3b8` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f3b8` | `0x8003f428` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f428` | `0x8003f498` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f498` | `0x8003f508` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f508` | `0x8003f578` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f578` | `0x8003f5e8` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f5e8` | `0x8003f658` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f658` | `0x8003f6c8` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003f6c8` | `0x8003f738` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003f738` | `0x8003f750` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003f750` | `0x8003f764` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003f764` | `0x8003f7f0` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003f7f0` | `0x8003f808` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003f808` | `0x8003f81c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003f81c` | `0x8003f8a4` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003f8a4` | `0x8003f8bc` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003f8bc` | `0x8003f8d0` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003f8d0` | `0x8003f8f0` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003f8f0` | `0x8003f8f8` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003f8f8` | `0x8003f904` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003f904` | `0x8003f908` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003f908` | `0x8003f98c` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003f98c` | `0x8003fa34` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fa34` | `0x8003fb68` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fb68` | `0x8003fc10` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003fc10` | `0x8003fd08` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003fd08` | `0x8003fda0` | 152 | `h_LT` | UNCONVERTED |
| `0x8003fda0` | `0x8003fe38` | 152 | `h_GT` | UNCONVERTED |
| `0x8003fe38` | `0x8003fecc` | 148 | `h_SLT` | UNCONVERTED |
| `0x8003fecc` | `0x8003ff60` | 148 | `h_SGT` | UNCONVERTED |
| `0x8003ff60` | `0x8003ffe4` | 132 | `h_EQ` | UNCONVERTED |
| `0x8003ffe4` | `0x80040044` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040044` | `0x800400b8` | 116 | `h_AND` | UNCONVERTED |
| `0x800400b8` | `0x8004012c` | 116 | `h_OR` | UNCONVERTED |
| `0x8004012c` | `0x800401a0` | 116 | `h_XOR` | UNCONVERTED |
| `0x800401a0` | `0x80040200` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040200` | `0x800402ec` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800402ec` | `0x8004048c` | 416 | `h_SHL` | UNCONVERTED |
| `0x8004048c` | `0x8004062c` | 416 | `h_SHR` | UNCONVERTED |
| `0x8004062c` | `0x800407e0` | 436 | `h_SAR` | UNCONVERTED |
| `0x800407e0` | `0x800408e0` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800408e0` | `0x80040914` | 52 | `h_POP` | UNCONVERTED |
| `0x80040914` | `0x80040c90` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80040c90` | `0x80040fa0` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80040fa0` | `0x800410d8` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x800410d8` | `0x8004111c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004111c` | `0x80041160` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041160` | `0x800411b0` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x800411b0` | `0x80041200` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041200` | `0x80041250` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041250` | `0x800412a0` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x800412a0` | `0x800412f0` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800412f0` | `0x80041340` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041340` | `0x80041390` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041390` | `0x800413e0` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800413e0` | `0x80041430` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041430` | `0x80041480` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041480` | `0x800414d0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800414d0` | `0x80041520` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041520` | `0x80041570` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041570` | `0x800415c0` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800415c0` | `0x80041610` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041610` | `0x800416a8` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800416a8` | `0x80041794` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041794` | `0x800417d8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800417d8` | `0x800419f4` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x800419f4` | `0x80041bdc` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041bdc` | `0x80041c20` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041c20` | `0x80041e04` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80041e04` | `0x80041e0c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80041e0c` | `0x80041ecc` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80041ecc` | `0x80041fc0` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80041fc0` | `0x80042004` | 68 | `h_PC` | UNCONVERTED |
| `0x80042004` | `0x8004228c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x8004228c` | `0x80042580` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042580` | `0x80042894` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042894` | `0x80042bc8` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042bc8` | `0x80042f1c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80042f1c` | `0x80043290` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043290` | `0x80043538` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043538` | `0x80043840` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043840` | `0x80043eac` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80043eac` | `0x8004446c` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x8004446c` | `0x800449ec` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800449ec` | `0x80045278` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045278` | `0x80045364` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045364` | `0x80045434` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045434` | `0x800456cc` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x800456cc` | `0x8004605c` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x8004605c` | `0x80046638` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046638` | `0x80046654` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046654` | `0x80047b78` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047b78` | `0x80047bc4` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047bc4` | `0x80047d80` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047d80` | `0x80048b48` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048b48` | `0x8004ad84` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004ad84` | `0x8004be8c` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004be8c` | `0x8004caec` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004caec` | `0x8004d8f4` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004d8f4` | `0x8004e554` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e554` | `0x8004ee0c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ee0c` | `0x8004f700` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004f700` | `0x8004fc9c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fc9c` | `0x80050348` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050348` | `0x80050368` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050368` | `0x80050a14` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050a14` | `0x80050a34` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050a34` | `0x80051364` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051364` | `0x800516b0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800516b0` | `0x80051820` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051820` | `0x80051824` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051824` | `0x800518ac` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800518ac` | `0x80051aa0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051aa0` | `0x80051ad0` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051ad0` | `0x80051ae4` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051ae4` | `0x80051af4` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051af4` | `0x80051b24` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051b24` | `0x80051d18` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80051d18` | `0x80051d48` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80051d48` | `0x80051d5c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80051d5c` | `0x80051d6c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80051d6c` | `0x80051d9c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80051d9c` | `0x80051dc0` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80051dc0` | `0x80051df0` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80051df0` | `0x80051fe4` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80051fe4` | `0x80052014` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052014` | `0x80052028` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052028` | `0x80052038` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052038` | `0x80052068` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052068` | `0x8005225c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005225c` | `0x8005228c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x8005228c` | `0x800522a0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800522a0` | `0x800522b0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800522b0` | `0x800522e0` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800522e0` | `0x800524d4` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800524d4` | `0x80052504` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052504` | `0x80052518` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052518` | `0x80052528` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052528` | `0x80052558` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052558` | `0x80052558` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052558` | `0x80052574` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800525ac` | `0x800525c8` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x800525c8` | `0x800525e4` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x800525e4` | `0x80052700` | 284 | `stage_system_call` | UNCONVERTED |
| `0x80052700` | `0x80052934` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80052934` | `0x80052d3c` | 1032 | `process_block_start_system_transactions` | UNCONVERTED |
| `0x80052d3c` | `0x80052e3c` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x80052e3c` | `0x80052f6c` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80052f6c` | `0x80052fc8` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80052fc8` | `0x80052fe8` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80052fe8` | `0x80053124` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053124` | `0x80053264` | 320 | `assemble_execution_requests` | UNCONVERTED |
| `0x800532f4` | `0x80053300` | 12 | `requests_hash_verify` | TAIL |
