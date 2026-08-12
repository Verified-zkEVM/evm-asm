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

`.text` = [0x80000000, 0x80053c34), 343092 bytes (`RegionMap.textSizeBytes = 0x53c34`)

- symbols in `.text`: 906 (448 converted, 458 unconverted)
- covered by converted `_prog`s: 120864 bytes (35.23%)
- NOT covered: 222228 bytes (64.77%), 459 ranges

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
| `0x8001871c` | `0x800194cc` | 3504 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800194cc` | `0x800196e8` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800199d0` | `0x80019a64` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a25c` | `0x8001a4b4` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a4b4` | `0x8001a72c` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a72c` | `0x8001a9c0` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001afb0` | `0x8001b268` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b630` | `0x8001b8a8` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b8a8` | `0x8001bb4c` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb4c` | `0x8001c628` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c930` | `0x8001c978` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d008` | `0x8001d1f0` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1f0` | `0x8001d24c` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d24c` | `0x8001d318` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d318` | `0x8001d3ec` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3ec` | `0x8001e314` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ebe8` | `0x8001ecfc` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ecfc` | `0x8001f004` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fcb8` | `0x8001fcf8` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff58` | `0x800200a0` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800200a0` | `0x800200d0` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020620` | `0x800207b0` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80020c7c` | `0x80020ebc` | 576 | `account_write_record` | UNCONVERTED |
| `0x800219a4` | `0x80021ac0` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021ac0` | `0x80021c84` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c84` | `0x80021f14` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800225e8` | `0x80022708` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023408` | `0x80023424` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023424` | `0x80023498` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023498` | `0x800234e8` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234e8` | `0x80023514` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023514` | `0x800235f4` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800235f4` | `0x80023674` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023674` | `0x800236a4` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237e4` | `0x800238a8` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800238a8` | `0x800238fc` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800238fc` | `0x8002392c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x8002392c` | `0x8002396c` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x8002396c` | `0x800239a4` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800239a4` | `0x800239e4` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b44` | `0x80023b5c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b1c` | `0x80024d18` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024db0` | `0x80024ebc` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024f20` | `0x800250e8` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250e8` | `0x800253d0` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800253d0` | `0x800254b8` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800254b8` | `0x80025594` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025594` | `0x8002566c` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259f0` | `0x80025b14` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025b14` | `0x80025c0c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026434` | `0x80026444` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026628` | `0x80026840` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026840` | `0x80026a34` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026dc8` | `0x8002744c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028368` | `0x80028884` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288e4` | `0x80028984` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029548` | `0x80029d3c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a3d0` | `0x8002a66c` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a66c` | `0x8002a6a4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c2fc` | `0x8002c7ec` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c7ec` | `0x8002d358` | 2924 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d358` | `0x8002d928` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d928` | `0x8002f2e8` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f2e8` | `0x8002f30c` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f30c` | `0x8002f328` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f328` | `0x8002f5ec` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f5ec` | `0x8002f5fc` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f5fc` | `0x8002f630` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f630` | `0x8002f648` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f648` | `0x8002f658` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f658` | `0x8002f68c` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f68c` | `0x8002f694` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f694` | `0x8002f740` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f740` | `0x8002f74c` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f74c` | `0x8002f774` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f774` | `0x8002f7b4` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f7b4` | `0x8002f7e4` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f7e4` | `0x8002f7e4` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f7e4` | `0x8002f7fc` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f7fc` | `0x8002f804` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f804` | `0x8002f810` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f810` | `0x8002f828` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f828` | `0x8002f840` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f840` | `0x8002f854` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f854` | `0x8002f874` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f874` | `0x8002f888` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f888` | `0x8002f8b4` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f8b4` | `0x8002f8fc` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f8fc` | `0x8002f9dc` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f9dc` | `0x8002fa8c` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fa8c` | `0x8002faac` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002faac` | `0x8002fb20` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fb20` | `0x8002fb30` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fb30` | `0x8002fb3c` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fb3c` | `0x8002fc20` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fc20` | `0x8002fc48` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fc48` | `0x8002fc5c` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fc5c` | `0x8002fc5c` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fc5c` | `0x8002fc5c` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fc5c` | `0x8002fc7c` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fc7c` | `0x8002fcac` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fcac` | `0x8002fcd0` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fcd0` | `0x8002fcf0` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fcf0` | `0x8002fcf4` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fcf4` | `0x8002fd80` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fd80` | `0x8002fd90` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fd90` | `0x8002fda0` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fda0` | `0x8002fed0` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fed0` | `0x8002fed0` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fed0` | `0x8003006c` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8003006c` | `0x8003006c` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8003006c` | `0x800300cc` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030e84` | `0x80030eac` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030eac` | `0x800310bc` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800311bc` | `0x80031268` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031268` | `0x800312ec` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800312ec` | `0x8003136c` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x8003136c` | `0x80031424` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031424` | `0x80031498` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031498` | `0x8003165c` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x8003165c` | `0x800316cc` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800316cc` | `0x80031744` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031744` | `0x800318f4` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800318f4` | `0x80031970` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031970` | `0x800319c0` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800319c0` | `0x80031a10` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031a10` | `0x80031a40` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031a40` | `0x80031a84` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031a84` | `0x80031ac8` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031ac8` | `0x80031b78` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031b78` | `0x80031cd4` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031cd4` | `0x80031fd0` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031fd0` | `0x800321ac` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800321ac` | `0x80032258` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032258` | `0x800323d0` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800323d0` | `0x8003259c` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x8003259c` | `0x800326d0` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800327c0` | `0x8003289c` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8003289c` | `0x800329ec` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800329ec` | `0x80032bc8` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032d78` | `0x80032f64` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032f64` | `0x80032fb8` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032fb8` | `0x80033000` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033000` | `0x800330d4` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800330d4` | `0x800331b4` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800331b4` | `0x8003336c` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033d84` | `0x80033e00` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033e00` | `0x80033eec` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034550` | `0x800345c0` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800345c0` | `0x80034620` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800349fc` | `0x80034a50` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034c18` | `0x80034e84` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034e84` | `0x800351c4` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800351c4` | `0x80035474` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035474` | `0x800357a8` | 820 | `bng2_double` | UNCONVERTED |
| `0x800357a8` | `0x80035b30` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035b30` | `0x80035c50` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035c70` | `0x800360a0` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800360a0` | `0x800364e4` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036538` | `0x800366e4` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036b58` | `0x80036d1c` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800374ac` | `0x80037784` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038070` | `0x80038100` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038100` | `0x800381d0` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800383a8` | `0x80038404` | 92 | `blq_sub` | UNCONVERTED |
| `0x800385f4` | `0x80038860` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038860` | `0x80038b80` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038b80` | `0x80038e30` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038e30` | `0x8003900c` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x8003900c` | `0x80039354` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800394a0` | `0x8003ad04` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ad04` | `0x8003bf40` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c064` | `0x8003c180` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c190` | `0x8003c1c0` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c1c0` | `0x8003c75c` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c75c` | `0x8003ca6c` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ca6c` | `0x8003ca74` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003ca74` | `0x8003ca78` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ca78` | `0x8003cc5c` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cd54` | `0x8003cf9c` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cf9c` | `0x8003d600` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d600` | `0x8003d71c` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d71c` | `0x8003d934` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d934` | `0x8003d974` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d974` | `0x8003d9bc` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d9bc` | `0x8003da0c` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003da0c` | `0x8003da64` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003da64` | `0x8003dac4` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dac4` | `0x8003db2c` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003db2c` | `0x8003db9c` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003db9c` | `0x8003dc14` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dc14` | `0x8003dc94` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dc94` | `0x8003dd1c` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dd1c` | `0x8003ddac` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003ddac` | `0x8003de44` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003de44` | `0x8003dee4` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dee4` | `0x8003df8c` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003df8c` | `0x8003e03c` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e03c` | `0x8003e0f4` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e0f4` | `0x8003e1b4` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e1b4` | `0x8003e27c` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e27c` | `0x8003e34c` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e34c` | `0x8003e424` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e424` | `0x8003e504` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e504` | `0x8003e5ec` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e5ec` | `0x8003e6dc` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e6dc` | `0x8003e7d4` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e7d4` | `0x8003e8d4` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e8d4` | `0x8003e9dc` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e9dc` | `0x8003eaec` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003eaec` | `0x8003ec04` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ec04` | `0x8003ed24` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ed24` | `0x8003ee4c` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ee4c` | `0x8003ef7c` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003ef7c` | `0x8003f0b4` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f0b4` | `0x8003f1f4` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f1f4` | `0x8003f26c` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f26c` | `0x8003f2e4` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f2e4` | `0x8003f35c` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f35c` | `0x8003f3d4` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f3d4` | `0x8003f44c` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f44c` | `0x8003f4c4` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f4c4` | `0x8003f53c` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f53c` | `0x8003f5b4` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f5b4` | `0x8003f62c` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f62c` | `0x8003f6a4` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f6a4` | `0x8003f71c` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f71c` | `0x8003f794` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f794` | `0x8003f80c` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f80c` | `0x8003f884` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f884` | `0x8003f8fc` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f8fc` | `0x8003f974` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f974` | `0x8003f9e4` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f9e4` | `0x8003fa54` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fa54` | `0x8003fac4` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fac4` | `0x8003fb34` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fb34` | `0x8003fba4` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fba4` | `0x8003fc14` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fc14` | `0x8003fc84` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fc84` | `0x8003fcf4` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fcf4` | `0x8003fd64` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fd64` | `0x8003fdd4` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fdd4` | `0x8003fe44` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fe44` | `0x8003feb4` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003feb4` | `0x8003ff24` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003ff24` | `0x8003ff94` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003ff94` | `0x80040004` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040004` | `0x80040074` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040074` | `0x8004008c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8004008c` | `0x800400a0` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800400a0` | `0x8004012c` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8004012c` | `0x80040144` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040144` | `0x80040158` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040158` | `0x800401e0` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800401e0` | `0x800401f8` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800401f8` | `0x8004020c` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8004020c` | `0x8004022c` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8004022c` | `0x80040234` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040234` | `0x80040240` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040240` | `0x80040244` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040244` | `0x800402c8` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800402c8` | `0x80040370` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040370` | `0x800404a4` | 308 | `h_MUL` | UNCONVERTED |
| `0x800404a4` | `0x8004054c` | 168 | `h_SUB` | UNCONVERTED |
| `0x8004054c` | `0x80040644` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040644` | `0x800406dc` | 152 | `h_LT` | UNCONVERTED |
| `0x800406dc` | `0x80040774` | 152 | `h_GT` | UNCONVERTED |
| `0x80040774` | `0x80040808` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040808` | `0x8004089c` | 148 | `h_SGT` | UNCONVERTED |
| `0x8004089c` | `0x80040920` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040920` | `0x80040980` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040980` | `0x800409f4` | 116 | `h_AND` | UNCONVERTED |
| `0x800409f4` | `0x80040a68` | 116 | `h_OR` | UNCONVERTED |
| `0x80040a68` | `0x80040adc` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040adc` | `0x80040b3c` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040b3c` | `0x80040c28` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040c28` | `0x80040dc8` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040dc8` | `0x80040f68` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040f68` | `0x8004111c` | 436 | `h_SAR` | UNCONVERTED |
| `0x8004111c` | `0x8004121c` | 256 | `h_CLZ` | UNCONVERTED |
| `0x8004121c` | `0x80041250` | 52 | `h_POP` | UNCONVERTED |
| `0x80041250` | `0x800415cc` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800415cc` | `0x800418dc` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x800418dc` | `0x80041a14` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041a14` | `0x80041a58` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041a58` | `0x80041a9c` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041a9c` | `0x80041aec` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041aec` | `0x80041b3c` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041b3c` | `0x80041b8c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041b8c` | `0x80041bdc` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041bdc` | `0x80041c2c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041c2c` | `0x80041c7c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041c7c` | `0x80041ccc` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041ccc` | `0x80041d1c` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041d1c` | `0x80041d6c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041d6c` | `0x80041dbc` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041dbc` | `0x80041e0c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041e0c` | `0x80041e5c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041e5c` | `0x80041eac` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041eac` | `0x80041efc` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041efc` | `0x80041f4c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041f4c` | `0x80041fe4` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041fe4` | `0x800420d0` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800420d0` | `0x80042114` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042114` | `0x80042330` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042330` | `0x80042518` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042518` | `0x8004255c` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x8004255c` | `0x80042740` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042740` | `0x80042748` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042748` | `0x80042808` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042808` | `0x800428fc` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x800428fc` | `0x80042940` | 68 | `h_PC` | UNCONVERTED |
| `0x80042940` | `0x80042bc8` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042bc8` | `0x80042ebc` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042ebc` | `0x800431d0` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800431d0` | `0x80043504` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043504` | `0x80043858` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043858` | `0x80043bcc` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043bcc` | `0x80043e74` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043e74` | `0x8004417c` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8004417c` | `0x800447e8` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x800447e8` | `0x80044da8` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044da8` | `0x80045328` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045328` | `0x80045bb4` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045bb4` | `0x80045ca0` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045ca0` | `0x80045d70` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045d70` | `0x80046008` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80046008` | `0x80046998` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046998` | `0x80046f74` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046f74` | `0x80046f90` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046f90` | `0x800484b4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800484b4` | `0x80048500` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048500` | `0x800486bc` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800486bc` | `0x80049484` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049484` | `0x8004b6c0` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b6c0` | `0x8004c7c8` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c7c8` | `0x8004d428` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d428` | `0x8004e230` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e230` | `0x8004ee90` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ee90` | `0x8004f748` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f748` | `0x8005003c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005003c` | `0x800505d8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800505d8` | `0x80050c84` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050c84` | `0x80050ca4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050ca4` | `0x80051350` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051350` | `0x80051370` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051370` | `0x80051ca0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051ca0` | `0x80051fec` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051fec` | `0x8005215c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005215c` | `0x80052160` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052160` | `0x800521e8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800521e8` | `0x800523dc` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800523dc` | `0x8005240c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005240c` | `0x80052420` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052420` | `0x80052430` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052430` | `0x80052460` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052460` | `0x80052654` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052654` | `0x80052684` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052684` | `0x80052698` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052698` | `0x800526a8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800526a8` | `0x800526d8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800526d8` | `0x800526fc` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x800526fc` | `0x8005272c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x8005272c` | `0x80052920` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052920` | `0x80052950` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052950` | `0x80052964` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052964` | `0x80052974` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052974` | `0x800529a4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800529a4` | `0x80052b98` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052b98` | `0x80052bc8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052bc8` | `0x80052bdc` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bdc` | `0x80052bec` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052bec` | `0x80052c1c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052c1c` | `0x80052e10` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052e10` | `0x80052e40` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052e40` | `0x80052e54` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e54` | `0x80052e64` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052e64` | `0x80052e94` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e94` | `0x80052e94` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052e94` | `0x80052eb0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005303c` | `0x80053270` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053770` | `0x800538a0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800538a0` | `0x800538fc` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800538fc` | `0x8005391c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005391c` | `0x80053a58` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053c28` | `0x80053c34` | 12 | `requests_hash_verify` | TAIL |
