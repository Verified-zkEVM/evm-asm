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

`.text` = [0x80000000, 0x80053eb0), 343728 bytes (`RegionMap.textSizeBytes = 0x53eb0`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121552 bytes (35.36%)
- NOT covered: 222176 bytes (64.64%), 458 ranges

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
| `0x8000e154` | `0x8000f470` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f8a0` | `0x8000fa80` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fa80` | `0x8000fb64` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fb64` | `0x8000fc40` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fc40` | `0x8000fcd4` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fcd4` | `0x8000fd90` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fd90` | `0x8000fe40` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fe40` | `0x8000ff24` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000ff24` | `0x8000ff60` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000ff60` | `0x80010090` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x80010090` | `0x800101b4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800101b4` | `0x80010264` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010264` | `0x800103e0` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800103e0` | `0x800104b8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800104b8` | `0x80010648` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010648` | `0x800107e4` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800107e4` | `0x80010894` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010894` | `0x800108fc` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x800108fc` | `0x80010998` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010998` | `0x80010fcc` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010fcc` | `0x800112b4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800112b4` | `0x8001160c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001160c` | `0x80011ae8` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011ae8` | `0x80011d8c` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011d8c` | `0x80011ea8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011ea8` | `0x80012160` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80012160` | `0x80012380` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012380` | `0x80012718` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012718` | `0x8001282c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001282c` | `0x8001284c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001284c` | `0x80012ad4` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012ad4` | `0x80012bb8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012bb8` | `0x80012c60` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012c60` | `0x80013394` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013394` | `0x800139cc` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013d08` | `0x80013d1c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d1c` | `0x80013d28` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013d28` | `0x80013d78` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013d78` | `0x80013d98` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013d98` | `0x80013dfc` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013dfc` | `0x800140a4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800140a4` | `0x800142f8` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x800142f8` | `0x800144ac` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800150ac` | `0x800152a4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155c4` | `0x800157f4` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015be4` | `0x800186e0` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800186e0` | `0x80019474` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019474` | `0x80019690` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019978` | `0x80019a0c` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a204` | `0x8001a45c` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a45c` | `0x8001a6d4` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a6d4` | `0x8001a968` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001af64` | `0x8001b280` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b648` | `0x8001b8c0` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b8c0` | `0x8001bb64` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb64` | `0x8001c628` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c93c` | `0x8001c984` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d014` | `0x8001d1fc` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1fc` | `0x8001d258` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d258` | `0x8001d324` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d324` | `0x8001d3f8` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3f8` | `0x8001e320` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ebf4` | `0x8001ed08` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ed08` | `0x8001f010` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fcc4` | `0x8001fd04` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff64` | `0x800200ac` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800200ac` | `0x800200dc` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8002062c` | `0x800207bc` | 400 | `destroy_storage` | UNCONVERTED |
| `0x800219b0` | `0x80021acc` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021acc` | `0x80021c90` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c90` | `0x80021f20` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800225f4` | `0x80022714` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023414` | `0x80023430` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023430` | `0x800234a4` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800234a4` | `0x800234f4` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234f4` | `0x80023520` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023520` | `0x80023600` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023600` | `0x80023680` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023680` | `0x800236b0` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237f0` | `0x800238b4` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800238b4` | `0x80023908` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023908` | `0x80023938` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023938` | `0x80023978` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023978` | `0x800239b0` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800239b0` | `0x800239f0` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b50` | `0x80023b68` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b28` | `0x80024d24` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024dbc` | `0x80024ec8` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024f2c` | `0x800250f4` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250f4` | `0x800253dc` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800253dc` | `0x800254c4` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800254c4` | `0x800255a0` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x800255a0` | `0x80025678` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259fc` | `0x80025b20` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025b20` | `0x80025c18` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026440` | `0x80026450` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026634` | `0x8002684c` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x8002684c` | `0x80026a40` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026dd4` | `0x80027458` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028374` | `0x80028890` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288f0` | `0x80028990` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800295dc` | `0x80029dd0` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a464` | `0x8002a700` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a700` | `0x8002a738` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c390` | `0x8002c888` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c888` | `0x8002d4ac` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d4ac` | `0x8002da7c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002da7c` | `0x8002f43c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f43c` | `0x8002f460` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f460` | `0x8002f47c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f47c` | `0x8002f740` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f740` | `0x8002f750` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f750` | `0x8002f784` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f784` | `0x8002f79c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f79c` | `0x8002f7ac` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f7ac` | `0x8002f7e0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f7e0` | `0x8002f7e8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f7e8` | `0x8002f894` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f894` | `0x8002f8a0` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f8a0` | `0x8002f8c8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f8c8` | `0x8002f908` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f908` | `0x8002f938` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f938` | `0x8002f938` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f938` | `0x8002f950` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f950` | `0x8002f958` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f958` | `0x8002f964` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f964` | `0x8002f97c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f97c` | `0x8002f994` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f994` | `0x8002f9a8` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f9a8` | `0x8002f9c8` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f9c8` | `0x8002f9dc` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f9dc` | `0x8002fa08` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fa08` | `0x8002fa50` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fa50` | `0x8002fb30` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fb30` | `0x8002fbe0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fbe0` | `0x8002fc00` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fc00` | `0x8002fc74` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fc74` | `0x8002fc84` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fc84` | `0x8002fc90` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fc90` | `0x8002fd74` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fd74` | `0x8002fd9c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fd9c` | `0x8002fdb0` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fdb0` | `0x8002fdb0` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fdb0` | `0x8002fdb0` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fdb0` | `0x8002fdd0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fdd0` | `0x8002fe00` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fe00` | `0x8002fe24` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fe24` | `0x8002fe44` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fe44` | `0x8002fe48` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fe48` | `0x8002fed4` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fed4` | `0x8002fee4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fee4` | `0x8002fef4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fef4` | `0x80030024` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x80030024` | `0x80030024` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x80030024` | `0x800301c0` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800301c0` | `0x800301c0` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800301c0` | `0x80030220` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030fd8` | `0x80031000` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031000` | `0x80031210` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031310` | `0x800313bc` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800313bc` | `0x80031440` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031440` | `0x800314c0` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800314c0` | `0x80031578` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031578` | `0x800315ec` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800315ec` | `0x800317b0` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800317b0` | `0x80031820` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031820` | `0x80031898` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031898` | `0x80031a48` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031a48` | `0x80031ac4` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031ac4` | `0x80031b14` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031b14` | `0x80031b64` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031b64` | `0x80031b94` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031b94` | `0x80031bd8` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031bd8` | `0x80031c1c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031c1c` | `0x80031ccc` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031ccc` | `0x80031e28` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031e28` | `0x80032124` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80032124` | `0x80032300` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032300` | `0x800323ac` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800323ac` | `0x80032524` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032524` | `0x800326f0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800326f0` | `0x80032824` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032914` | `0x800329f0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800329f0` | `0x80032b40` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032b40` | `0x80032d1c` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032ecc` | `0x800330b8` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800330b8` | `0x8003310c` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x8003310c` | `0x80033154` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033154` | `0x80033228` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033228` | `0x80033308` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033308` | `0x800334c0` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033ed8` | `0x80033f54` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033f54` | `0x80034040` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800346a4` | `0x80034714` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034714` | `0x80034774` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034b50` | `0x80034ba4` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034d6c` | `0x80034fd8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034fd8` | `0x80035318` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035318` | `0x800355c8` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800355c8` | `0x800358fc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800358fc` | `0x80035c84` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035c84` | `0x80035da4` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035dc4` | `0x800361f4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800361f4` | `0x80036638` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003668c` | `0x80036838` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036cac` | `0x80036e70` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037600` | `0x800378d8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800381c4` | `0x80038254` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038254` | `0x80038324` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800384fc` | `0x80038558` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038748` | `0x800389b4` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x800389b4` | `0x80038cd4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038cd4` | `0x80038f84` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038f84` | `0x80039160` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039160` | `0x800394a8` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800395f4` | `0x8003ae58` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ae58` | `0x8003c094` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c1b8` | `0x8003c2d4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c2e4` | `0x8003c314` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c314` | `0x8003c8b0` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c8b0` | `0x8003cbc0` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cbc0` | `0x8003cbc8` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cbc8` | `0x8003cbcc` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cbcc` | `0x8003cdb0` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cea8` | `0x8003d0f0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d0f0` | `0x8003d754` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d754` | `0x8003d870` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d870` | `0x8003da88` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003da88` | `0x8003dac8` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003dac8` | `0x8003db10` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003db10` | `0x8003db60` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003db60` | `0x8003dbb8` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dbb8` | `0x8003dc18` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dc18` | `0x8003dc80` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dc80` | `0x8003dcf0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dcf0` | `0x8003dd68` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dd68` | `0x8003dde8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dde8` | `0x8003de70` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003de70` | `0x8003df00` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003df00` | `0x8003df98` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003df98` | `0x8003e038` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e038` | `0x8003e0e0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e0e0` | `0x8003e190` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e190` | `0x8003e248` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e248` | `0x8003e308` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e308` | `0x8003e3d0` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e3d0` | `0x8003e4a0` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e4a0` | `0x8003e578` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e578` | `0x8003e658` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e658` | `0x8003e740` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e740` | `0x8003e830` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e830` | `0x8003e928` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e928` | `0x8003ea28` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ea28` | `0x8003eb30` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003eb30` | `0x8003ec40` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ec40` | `0x8003ed58` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ed58` | `0x8003ee78` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ee78` | `0x8003efa0` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003efa0` | `0x8003f0d0` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f0d0` | `0x8003f208` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f208` | `0x8003f348` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f348` | `0x8003f3c0` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f3c0` | `0x8003f438` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f438` | `0x8003f4b0` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f4b0` | `0x8003f528` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f528` | `0x8003f5a0` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f5a0` | `0x8003f618` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f618` | `0x8003f690` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f690` | `0x8003f708` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f708` | `0x8003f780` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f780` | `0x8003f7f8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f7f8` | `0x8003f870` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f870` | `0x8003f8e8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f8e8` | `0x8003f960` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f960` | `0x8003f9d8` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f9d8` | `0x8003fa50` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fa50` | `0x8003fac8` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fac8` | `0x8003fb38` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fb38` | `0x8003fba8` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fba8` | `0x8003fc18` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fc18` | `0x8003fc88` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fc88` | `0x8003fcf8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fcf8` | `0x8003fd68` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fd68` | `0x8003fdd8` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fdd8` | `0x8003fe48` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fe48` | `0x8003feb8` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003feb8` | `0x8003ff28` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003ff28` | `0x8003ff98` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003ff98` | `0x80040008` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040008` | `0x80040078` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040078` | `0x800400e8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800400e8` | `0x80040158` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040158` | `0x800401c8` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800401c8` | `0x800401e0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800401e0` | `0x800401f4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800401f4` | `0x80040280` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040280` | `0x80040298` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040298` | `0x800402ac` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800402ac` | `0x80040334` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040334` | `0x8004034c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8004034c` | `0x80040360` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040360` | `0x80040380` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040380` | `0x80040388` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040388` | `0x80040394` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040394` | `0x80040398` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040398` | `0x8004041c` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8004041c` | `0x800404c4` | 168 | `h_ADD` | UNCONVERTED |
| `0x800404c4` | `0x800405f8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800405f8` | `0x800406a0` | 168 | `h_SUB` | UNCONVERTED |
| `0x800406a0` | `0x80040798` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040798` | `0x80040830` | 152 | `h_LT` | UNCONVERTED |
| `0x80040830` | `0x800408c8` | 152 | `h_GT` | UNCONVERTED |
| `0x800408c8` | `0x8004095c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004095c` | `0x800409f0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800409f0` | `0x80040a74` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040a74` | `0x80040ad4` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040ad4` | `0x80040b48` | 116 | `h_AND` | UNCONVERTED |
| `0x80040b48` | `0x80040bbc` | 116 | `h_OR` | UNCONVERTED |
| `0x80040bbc` | `0x80040c30` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040c30` | `0x80040c90` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040c90` | `0x80040d7c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040d7c` | `0x80040f1c` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040f1c` | `0x800410bc` | 416 | `h_SHR` | UNCONVERTED |
| `0x800410bc` | `0x80041270` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041270` | `0x80041370` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041370` | `0x800413a4` | 52 | `h_POP` | UNCONVERTED |
| `0x800413a4` | `0x80041720` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80041720` | `0x80041a30` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80041a30` | `0x80041b68` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041b68` | `0x80041bac` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041bac` | `0x80041bf0` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041bf0` | `0x80041c40` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041c40` | `0x80041c90` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041c90` | `0x80041ce0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041ce0` | `0x80041d30` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041d30` | `0x80041d80` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041d80` | `0x80041dd0` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041dd0` | `0x80041e20` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041e20` | `0x80041e70` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041e70` | `0x80041ec0` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041ec0` | `0x80041f10` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041f10` | `0x80041f60` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041f60` | `0x80041fb0` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041fb0` | `0x80042000` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042000` | `0x80042050` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042050` | `0x800420a0` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800420a0` | `0x80042138` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042138` | `0x80042224` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042224` | `0x80042268` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042268` | `0x80042484` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042484` | `0x8004266c` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x8004266c` | `0x800426b0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800426b0` | `0x80042894` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042894` | `0x8004289c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x8004289c` | `0x8004295c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004295c` | `0x80042a50` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042a50` | `0x80042a94` | 68 | `h_PC` | UNCONVERTED |
| `0x80042a94` | `0x80042d1c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042d1c` | `0x80043010` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80043010` | `0x80043324` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043324` | `0x80043658` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043658` | `0x800439ac` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800439ac` | `0x80043d20` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043d20` | `0x80043fc8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043fc8` | `0x800442d0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800442d0` | `0x8004493c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004493c` | `0x80044efc` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044efc` | `0x8004547c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x8004547c` | `0x80045d08` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045d08` | `0x80045df4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045df4` | `0x80045ec4` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045ec4` | `0x8004615c` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x8004615c` | `0x80046aec` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046aec` | `0x800470c8` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x800470c8` | `0x800470e4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800470e4` | `0x80048608` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048608` | `0x80048654` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048654` | `0x80048810` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048810` | `0x800495d8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800495d8` | `0x8004b894` | 8892 | `h_CALL` | UNCONVERTED |
| `0x8004b894` | `0x8004ca1c` | 4488 | `h_CALLCODE` | UNCONVERTED |
| `0x8004ca1c` | `0x8004d690` | 3188 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d690` | `0x8004e498` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e498` | `0x8004f10c` | 3188 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f10c` | `0x8004f9c4` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f9c4` | `0x800502b8` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800502b8` | `0x80050854` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050854` | `0x80050f00` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050f00` | `0x80050f20` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050f20` | `0x800515cc` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800515cc` | `0x800515ec` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800515ec` | `0x80051f1c` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051f1c` | `0x80052268` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052268` | `0x800523d8` | 368 | `h_STOP` | UNCONVERTED |
| `0x800523d8` | `0x800523dc` | 4 | `h_invalid` | UNCONVERTED |
| `0x800523dc` | `0x80052464` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80052464` | `0x80052658` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052658` | `0x80052688` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052688` | `0x8005269c` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x8005269c` | `0x800526ac` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x800526ac` | `0x800526dc` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800526dc` | `0x800528d0` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x800528d0` | `0x80052900` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052900` | `0x80052914` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052914` | `0x80052924` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052924` | `0x80052954` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052954` | `0x80052978` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052978` | `0x800529a8` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x800529a8` | `0x80052b9c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052b9c` | `0x80052bcc` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052bcc` | `0x80052be0` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052be0` | `0x80052bf0` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052bf0` | `0x80052c20` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052c20` | `0x80052e14` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052e14` | `0x80052e44` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052e44` | `0x80052e58` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e58` | `0x80052e68` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052e68` | `0x80052e98` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e98` | `0x8005308c` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x8005308c` | `0x800530bc` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800530bc` | `0x800530d0` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800530d0` | `0x800530e0` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800530e0` | `0x80053110` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053110` | `0x80053110` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053110` | `0x8005312c` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800532b8` | `0x800534ec` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800539ec` | `0x80053b1c` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053b1c` | `0x80053b78` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053b78` | `0x80053b98` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053b98` | `0x80053cd4` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053ea4` | `0x80053eb0` | 12 | `requests_hash_verify` | TAIL |
