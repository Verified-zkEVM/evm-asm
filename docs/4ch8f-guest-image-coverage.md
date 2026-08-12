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
not linked** (96 of 544 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053c38), 343096 bytes (`RegionMap.textSizeBytes = 0x53c38`)

- symbols in `.text`: 906 (448 converted, 458 unconverted)
- covered by converted `_prog`s: 120864 bytes (35.23%)
- NOT covered: 222232 bytes (64.77%), 459 ranges

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
| `0x80009b84` | `0x80009d48` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009d48` | `0x80009db4` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a670` | `0x8000a870` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a870` | `0x8000a9b0` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a9b0` | `0x8000ac6c` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000ac6c` | `0x8000ad5c` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ad5c` | `0x8000aecc` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e184` | `0x8000f4a0` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f8d0` | `0x8000fab0` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fab0` | `0x8000fb94` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fb94` | `0x8000fc70` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fc70` | `0x8000fd04` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fd04` | `0x8000fdc0` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fdc0` | `0x8000fe70` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fe70` | `0x8000ff54` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000ff54` | `0x8000ff90` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000ff90` | `0x800100c0` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x800100c0` | `0x800101e4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800101e4` | `0x80010294` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010294` | `0x80010410` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010410` | `0x800104e8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800104e8` | `0x80010678` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010678` | `0x80010814` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010814` | `0x800108c4` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800108c4` | `0x8001092c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8001092c` | `0x800109c8` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800109c8` | `0x80010ffc` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010ffc` | `0x800112e4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800112e4` | `0x8001163c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001163c` | `0x80011b18` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011b18` | `0x80011dbc` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011dbc` | `0x80011ed8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011ed8` | `0x80012190` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80012190` | `0x800123b0` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800123b0` | `0x80012748` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012748` | `0x8001285c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001285c` | `0x8001287c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001287c` | `0x80012b04` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012b04` | `0x80012be8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012be8` | `0x80012c90` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012c90` | `0x800133c4` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800133c4` | `0x800139fc` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013d38` | `0x80013d4c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d4c` | `0x80013d58` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013d58` | `0x80013da8` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013da8` | `0x80013dc8` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013dc8` | `0x80013e2c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013e2c` | `0x800140d4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800140d4` | `0x80014328` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014328` | `0x800144dc` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800150dc` | `0x800152d4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155f4` | `0x80015824` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015c14` | `0x8001871c` | 11016 | `block_verdict` | UNCONVERTED |
| `0x8001871c` | `0x800194d0` | 3508 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800194d0` | `0x800196ec` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800199d4` | `0x80019a68` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a260` | `0x8001a4b8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a4b8` | `0x8001a730` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a730` | `0x8001a9c4` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001afb4` | `0x8001b26c` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b634` | `0x8001b8ac` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b8ac` | `0x8001bb50` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb50` | `0x8001c62c` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c934` | `0x8001c97c` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d00c` | `0x8001d1f4` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1f4` | `0x8001d250` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d250` | `0x8001d31c` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d31c` | `0x8001d3f0` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3f0` | `0x8001e318` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ebec` | `0x8001ed00` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ed00` | `0x8001f008` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fcbc` | `0x8001fcfc` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff5c` | `0x800200a4` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800200a4` | `0x800200d4` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020624` | `0x800207b4` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80020c80` | `0x80020ec0` | 576 | `account_write_record` | UNCONVERTED |
| `0x800219a8` | `0x80021ac4` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021ac4` | `0x80021c88` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c88` | `0x80021f18` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800225ec` | `0x8002270c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x8002340c` | `0x80023428` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023428` | `0x8002349c` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x8002349c` | `0x800234ec` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234ec` | `0x80023518` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023518` | `0x800235f8` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800235f8` | `0x80023678` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023678` | `0x800236a8` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237e8` | `0x800238ac` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800238ac` | `0x80023900` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023900` | `0x80023930` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023930` | `0x80023970` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023970` | `0x800239a8` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800239a8` | `0x800239e8` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b48` | `0x80023b60` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b20` | `0x80024d1c` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024db4` | `0x80024ec0` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024f24` | `0x800250ec` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250ec` | `0x800253d4` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800253d4` | `0x800254bc` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800254bc` | `0x80025598` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025598` | `0x80025670` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259f4` | `0x80025b18` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025b18` | `0x80025c10` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026438` | `0x80026448` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x8002662c` | `0x80026844` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026844` | `0x80026a38` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026dcc` | `0x80027450` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x8002836c` | `0x80028888` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288e8` | `0x80028988` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x8002954c` | `0x80029d40` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a3d4` | `0x8002a670` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a670` | `0x8002a6a8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c300` | `0x8002c7f0` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c7f0` | `0x8002d35c` | 2924 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d35c` | `0x8002d92c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d92c` | `0x8002f2ec` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f2ec` | `0x8002f310` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f310` | `0x8002f32c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f32c` | `0x8002f5f0` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f5f0` | `0x8002f600` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f600` | `0x8002f634` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f634` | `0x8002f64c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f64c` | `0x8002f65c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f65c` | `0x8002f690` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f690` | `0x8002f698` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f698` | `0x8002f744` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f744` | `0x8002f750` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f750` | `0x8002f778` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f778` | `0x8002f7b8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f7b8` | `0x8002f7e8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f7e8` | `0x8002f7e8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f7e8` | `0x8002f800` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f800` | `0x8002f808` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f808` | `0x8002f814` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f814` | `0x8002f82c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f82c` | `0x8002f844` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f844` | `0x8002f858` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f858` | `0x8002f878` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f878` | `0x8002f88c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f88c` | `0x8002f8b8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f8b8` | `0x8002f900` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f900` | `0x8002f9e0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f9e0` | `0x8002fa90` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fa90` | `0x8002fab0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fab0` | `0x8002fb24` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fb24` | `0x8002fb34` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fb34` | `0x8002fb40` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fb40` | `0x8002fc24` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fc24` | `0x8002fc4c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fc4c` | `0x8002fc60` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fc60` | `0x8002fc60` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fc60` | `0x8002fc60` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fc60` | `0x8002fc80` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fc80` | `0x8002fcb0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fcb0` | `0x8002fcd4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fcd4` | `0x8002fcf4` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fcf4` | `0x8002fcf8` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fcf8` | `0x8002fd84` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fd84` | `0x8002fd94` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fd94` | `0x8002fda4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fda4` | `0x8002fed4` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fed4` | `0x8002fed4` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fed4` | `0x80030070` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030070` | `0x80030070` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030070` | `0x800300d0` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030e88` | `0x80030eb0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030eb0` | `0x800310c0` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800311c0` | `0x8003126c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x8003126c` | `0x800312f0` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800312f0` | `0x80031370` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031370` | `0x80031428` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031428` | `0x8003149c` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x8003149c` | `0x80031660` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031660` | `0x800316d0` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800316d0` | `0x80031748` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031748` | `0x800318f8` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800318f8` | `0x80031974` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031974` | `0x800319c4` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800319c4` | `0x80031a14` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031a14` | `0x80031a44` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031a44` | `0x80031a88` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031a88` | `0x80031acc` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031acc` | `0x80031b7c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031b7c` | `0x80031cd8` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031cd8` | `0x80031fd4` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031fd4` | `0x800321b0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800321b0` | `0x8003225c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x8003225c` | `0x800323d4` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800323d4` | `0x800325a0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800325a0` | `0x800326d4` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800327c4` | `0x800328a0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800328a0` | `0x800329f0` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800329f0` | `0x80032bcc` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032d7c` | `0x80032f68` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032f68` | `0x80032fbc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032fbc` | `0x80033004` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033004` | `0x800330d8` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800330d8` | `0x800331b8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800331b8` | `0x80033370` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033d88` | `0x80033e04` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033e04` | `0x80033ef0` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034554` | `0x800345c4` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800345c4` | `0x80034624` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034a00` | `0x80034a54` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034c1c` | `0x80034e88` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034e88` | `0x800351c8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800351c8` | `0x80035478` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035478` | `0x800357ac` | 820 | `bng2_double` | UNCONVERTED |
| `0x800357ac` | `0x80035b34` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035b34` | `0x80035c54` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035c74` | `0x800360a4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800360a4` | `0x800364e8` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003653c` | `0x800366e8` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036b5c` | `0x80036d20` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800374b0` | `0x80037788` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038074` | `0x80038104` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038104` | `0x800381d4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800383ac` | `0x80038408` | 92 | `blq_sub` | UNCONVERTED |
| `0x800385f8` | `0x80038864` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038864` | `0x80038b84` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038b84` | `0x80038e34` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038e34` | `0x80039010` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039010` | `0x80039358` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800394a4` | `0x8003ad08` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ad08` | `0x8003bf44` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c068` | `0x8003c184` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c194` | `0x8003c1c4` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c1c4` | `0x8003c760` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c760` | `0x8003ca70` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ca70` | `0x8003ca78` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003ca78` | `0x8003ca7c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ca7c` | `0x8003cc60` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cd58` | `0x8003cfa0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cfa0` | `0x8003d604` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d604` | `0x8003d720` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d720` | `0x8003d938` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d938` | `0x8003d978` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d978` | `0x8003d9c0` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d9c0` | `0x8003da10` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003da10` | `0x8003da68` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003da68` | `0x8003dac8` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dac8` | `0x8003db30` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003db30` | `0x8003dba0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dba0` | `0x8003dc18` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dc18` | `0x8003dc98` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dc98` | `0x8003dd20` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dd20` | `0x8003ddb0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003ddb0` | `0x8003de48` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003de48` | `0x8003dee8` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dee8` | `0x8003df90` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003df90` | `0x8003e040` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e040` | `0x8003e0f8` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e0f8` | `0x8003e1b8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e1b8` | `0x8003e280` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e280` | `0x8003e350` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e350` | `0x8003e428` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e428` | `0x8003e508` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e508` | `0x8003e5f0` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e5f0` | `0x8003e6e0` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e6e0` | `0x8003e7d8` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e7d8` | `0x8003e8d8` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e8d8` | `0x8003e9e0` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e9e0` | `0x8003eaf0` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003eaf0` | `0x8003ec08` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ec08` | `0x8003ed28` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ed28` | `0x8003ee50` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ee50` | `0x8003ef80` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003ef80` | `0x8003f0b8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f0b8` | `0x8003f1f8` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f1f8` | `0x8003f270` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f270` | `0x8003f2e8` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f2e8` | `0x8003f360` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f360` | `0x8003f3d8` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f3d8` | `0x8003f450` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f450` | `0x8003f4c8` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f4c8` | `0x8003f540` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f540` | `0x8003f5b8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f5b8` | `0x8003f630` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f630` | `0x8003f6a8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f6a8` | `0x8003f720` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f720` | `0x8003f798` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f798` | `0x8003f810` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f810` | `0x8003f888` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f888` | `0x8003f900` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f900` | `0x8003f978` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f978` | `0x8003f9e8` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f9e8` | `0x8003fa58` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fa58` | `0x8003fac8` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fac8` | `0x8003fb38` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fb38` | `0x8003fba8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fba8` | `0x8003fc18` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fc18` | `0x8003fc88` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fc88` | `0x8003fcf8` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fcf8` | `0x8003fd68` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fd68` | `0x8003fdd8` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fdd8` | `0x8003fe48` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fe48` | `0x8003feb8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003feb8` | `0x8003ff28` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003ff28` | `0x8003ff98` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003ff98` | `0x80040008` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040008` | `0x80040078` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040078` | `0x80040090` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040090` | `0x800400a4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800400a4` | `0x80040130` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040130` | `0x80040148` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040148` | `0x8004015c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8004015c` | `0x800401e4` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800401e4` | `0x800401fc` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800401fc` | `0x80040210` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040210` | `0x80040230` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040230` | `0x80040238` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040238` | `0x80040244` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040244` | `0x80040248` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040248` | `0x800402cc` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800402cc` | `0x80040374` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040374` | `0x800404a8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800404a8` | `0x80040550` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040550` | `0x80040648` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040648` | `0x800406e0` | 152 | `h_LT` | UNCONVERTED |
| `0x800406e0` | `0x80040778` | 152 | `h_GT` | UNCONVERTED |
| `0x80040778` | `0x8004080c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004080c` | `0x800408a0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800408a0` | `0x80040924` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040924` | `0x80040984` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040984` | `0x800409f8` | 116 | `h_AND` | UNCONVERTED |
| `0x800409f8` | `0x80040a6c` | 116 | `h_OR` | UNCONVERTED |
| `0x80040a6c` | `0x80040ae0` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040ae0` | `0x80040b40` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040b40` | `0x80040c2c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040c2c` | `0x80040dcc` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040dcc` | `0x80040f6c` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040f6c` | `0x80041120` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041120` | `0x80041220` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041220` | `0x80041254` | 52 | `h_POP` | UNCONVERTED |
| `0x80041254` | `0x800415d0` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800415d0` | `0x800418e0` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x800418e0` | `0x80041a18` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041a18` | `0x80041a5c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041a5c` | `0x80041aa0` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041aa0` | `0x80041af0` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041af0` | `0x80041b40` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041b40` | `0x80041b90` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041b90` | `0x80041be0` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041be0` | `0x80041c30` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041c30` | `0x80041c80` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041c80` | `0x80041cd0` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041cd0` | `0x80041d20` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041d20` | `0x80041d70` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041d70` | `0x80041dc0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041dc0` | `0x80041e10` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041e10` | `0x80041e60` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041e60` | `0x80041eb0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041eb0` | `0x80041f00` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041f00` | `0x80041f50` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041f50` | `0x80041fe8` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041fe8` | `0x800420d4` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800420d4` | `0x80042118` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042118` | `0x80042334` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042334` | `0x8004251c` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x8004251c` | `0x80042560` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042560` | `0x80042744` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042744` | `0x8004274c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x8004274c` | `0x8004280c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004280c` | `0x80042900` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042900` | `0x80042944` | 68 | `h_PC` | UNCONVERTED |
| `0x80042944` | `0x80042bcc` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042bcc` | `0x80042ec0` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042ec0` | `0x800431d4` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800431d4` | `0x80043508` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043508` | `0x8004385c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x8004385c` | `0x80043bd0` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043bd0` | `0x80043e78` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043e78` | `0x80044180` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044180` | `0x800447ec` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x800447ec` | `0x80044dac` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044dac` | `0x8004532c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x8004532c` | `0x80045bb8` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045bb8` | `0x80045ca4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045ca4` | `0x80045d74` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045d74` | `0x8004600c` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x8004600c` | `0x8004699c` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x8004699c` | `0x80046f78` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046f78` | `0x80046f94` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046f94` | `0x800484b8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800484b8` | `0x80048504` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048504` | `0x800486c0` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800486c0` | `0x80049488` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049488` | `0x8004b6c4` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b6c4` | `0x8004c7cc` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c7cc` | `0x8004d42c` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d42c` | `0x8004e234` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e234` | `0x8004ee94` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ee94` | `0x8004f74c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f74c` | `0x80050040` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050040` | `0x800505dc` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800505dc` | `0x80050c88` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050c88` | `0x80050ca8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050ca8` | `0x80051354` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051354` | `0x80051374` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051374` | `0x80051ca4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051ca4` | `0x80051ff0` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051ff0` | `0x80052160` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052160` | `0x80052164` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052164` | `0x800521ec` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800521ec` | `0x800523e0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800523e0` | `0x80052410` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052410` | `0x80052424` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052424` | `0x80052434` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052434` | `0x80052464` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052464` | `0x80052658` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052658` | `0x80052688` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052688` | `0x8005269c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x8005269c` | `0x800526ac` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800526ac` | `0x800526dc` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800526dc` | `0x80052700` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052700` | `0x80052730` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052730` | `0x80052924` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052924` | `0x80052954` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052954` | `0x80052968` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052968` | `0x80052978` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052978` | `0x800529a8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800529a8` | `0x80052b9c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052b9c` | `0x80052bcc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052bcc` | `0x80052be0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052be0` | `0x80052bf0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052bf0` | `0x80052c20` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052c20` | `0x80052e14` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052e14` | `0x80052e44` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052e44` | `0x80052e58` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e58` | `0x80052e68` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052e68` | `0x80052e98` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e98` | `0x80052e98` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052e98` | `0x80052eb4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053040` | `0x80053274` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053774` | `0x800538a4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800538a4` | `0x80053900` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053900` | `0x80053920` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053920` | `0x80053a5c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053c2c` | `0x80053c38` | 12 | `requests_hash_verify` | TAIL |
