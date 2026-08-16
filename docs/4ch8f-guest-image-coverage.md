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
not linked** (104 of 547 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053b90), 342928 bytes (`RegionMap.textSizeBytes = 0x53b90`)

- symbols in `.text`: 907 (443 converted, 464 unconverted)
- covered by converted `_prog`s: 119632 bytes (34.89%)
- NOT covered: 223296 bytes (65.11%), 465 ranges

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
| `0x80000000` | `0x800018c0` | 6336 | `_start` | UNCONVERTED |
| `0x800020c0` | `0x800020f0` | 48 | `sg_load_u32le` | UNCONVERTED |
| `0x800020f0` | `0x80002110` | 32 | `sg_memcpy` | UNCONVERTED |
| `0x80002110` | `0x80002134` | 36 | `sg_validate_fixed_list` | UNCONVERTED |
| `0x80002134` | `0x800021ec` | 184 | `sg_validate_var_list` | UNCONVERTED |
| `0x800021ec` | `0x800022d8` | 236 | `sg_validate_execution_payload` | UNCONVERTED |
| `0x800022d8` | `0x80002410` | 312 | `sg_validate_execution_requests` | UNCONVERTED |
| `0x80002410` | `0x800024e0` | 208 | `sg_validate_npr` | UNCONVERTED |
| `0x800024e0` | `0x800025ac` | 204 | `sg_validate_witness` | UNCONVERTED |
| `0x800025ac` | `0x800026c0` | 276 | `sg_validate_chain_config` | UNCONVERTED |
| `0x800026c0` | `0x800028f0` | 560 | `ssz_htr_withdrawals` | UNCONVERTED |
| `0x800028f0` | `0x80002954` | 100 | `sg_htr_bv48` | UNCONVERTED |
| `0x80002954` | `0x800029ac` | 88 | `sg_htr_bv96` | UNCONVERTED |
| `0x800029ac` | `0x80002a8c` | 224 | `sg_htr_deposit` | UNCONVERTED |
| `0x80002a8c` | `0x80002b40` | 180 | `sg_htr_wr` | UNCONVERTED |
| `0x80002b40` | `0x80002bd8` | 152 | `sg_htr_cr` | UNCONVERTED |
| `0x80002bd8` | `0x80002c88` | 176 | `sg_htr_bd` | UNCONVERTED |
| `0x80002c88` | `0x80002d0c` | 132 | `sg_htr_be` | UNCONVERTED |
| `0x80002d0c` | `0x80002e0c` | 256 | `sg_htr_clist` | UNCONVERTED |
| `0x80002e0c` | `0x80002f84` | 376 | `ssz_htr_execution_requests` | UNCONVERTED |
| `0x80004b34` | `0x80004c08` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80004c08` | `0x80004cdc` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004fdc` | `0x80005024` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80005024` | `0x8000508c` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x8000508c` | `0x800050e4` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x800050e4` | `0x8000514c` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x8000514c` | `0x80005340` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x8000961c` | `0x800097e0` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x800097e0` | `0x8000984c` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a108` | `0x8000a308` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a308` | `0x8000a448` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a448` | `0x8000a704` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a704` | `0x8000a7f4` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a7f4` | `0x8000a964` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000dec8` | `0x8000f1e4` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f614` | `0x8000f7f4` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f7f4` | `0x8000f8d8` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f8d8` | `0x8000f9b4` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f9b4` | `0x8000fa48` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fa48` | `0x8000fb04` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fb04` | `0x8000fbb4` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fbb4` | `0x8000fc98` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000fc98` | `0x8000fcd4` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000fcd4` | `0x8000fe04` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000fe04` | `0x8000ff28` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000ff28` | `0x8000ffd8` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000ffd8` | `0x80010154` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010154` | `0x8001022c` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8001022c` | `0x800103bc` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x800103bc` | `0x80010558` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010558` | `0x80010608` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010608` | `0x80010670` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010670` | `0x8001070c` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x8001070c` | `0x80010d40` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010d40` | `0x80011028` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011028` | `0x80011380` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011380` | `0x8001185c` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x8001185c` | `0x80011b00` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011b00` | `0x80011c1c` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011c1c` | `0x80011ed4` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011ed4` | `0x800120f4` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800120f4` | `0x8001248c` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x8001248c` | `0x800125a0` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x800125a0` | `0x800125c0` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x800125c0` | `0x80012848` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012848` | `0x8001292c` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x8001292c` | `0x800129d4` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800129d4` | `0x80013108` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013108` | `0x80013740` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013a7c` | `0x80013a90` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013a90` | `0x80013a9c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013a9c` | `0x80013aec` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013aec` | `0x80013b0c` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013b0c` | `0x80013b70` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013b70` | `0x80013e18` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013e18` | `0x8001406c` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x8001406c` | `0x80014220` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80014e20` | `0x80015018` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015338` | `0x80015568` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015958` | `0x80018454` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80018454` | `0x800191e8` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800191e8` | `0x80019404` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800196ec` | `0x80019780` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019f78` | `0x8001a1d0` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a1d0` | `0x8001a448` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a448` | `0x8001a6dc` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001acd8` | `0x8001aff4` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b3bc` | `0x8001b634` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b634` | `0x8001b8d8` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b8d8` | `0x8001c39c` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c6b0` | `0x8001c6f8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001cd88` | `0x8001cf70` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001cf70` | `0x8001cfcc` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001cfcc` | `0x8001d098` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d098` | `0x8001d16c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d16c` | `0x8001e0ec` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e9c0` | `0x8001ead4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ead4` | `0x8001eddc` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fa90` | `0x8001fad0` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fd30` | `0x8001fe78` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001fe78` | `0x8001fea8` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x800203f8` | `0x80020588` | 400 | `destroy_storage` | UNCONVERTED |
| `0x8002177c` | `0x80021898` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021898` | `0x80021a5c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021a5c` | `0x80021cec` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800223c0` | `0x800224e0` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800231e0` | `0x800231fc` | 28 | `keccak_init` | UNCONVERTED |
| `0x800231fc` | `0x80023270` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023270` | `0x800232c0` | 80 | `keccak_final` | UNCONVERTED |
| `0x800232c0` | `0x800232ec` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800232ec` | `0x800233cc` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800233cc` | `0x8002344c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x8002344c` | `0x8002347c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800235bc` | `0x80023680` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023680` | `0x800236d4` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800236d4` | `0x80023704` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023704` | `0x80023744` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023744` | `0x8002377c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002377c` | `0x800237bc` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x8002391c` | `0x80023934` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800248f4` | `0x80024af0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024b88` | `0x80024c94` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024cf8` | `0x80024ec0` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024ec0` | `0x800251a8` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800251a8` | `0x80025290` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025290` | `0x8002536c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x8002536c` | `0x80025444` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800257f8` | `0x8002591c` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x8002591c` | `0x80025a14` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x8002623c` | `0x8002624c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026430` | `0x80026648` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026648` | `0x8002683c` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026bd0` | `0x80027254` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028170` | `0x8002868c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800286ec` | `0x8002878c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800293d8` | `0x80029bcc` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a260` | `0x8002a4fc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a4fc` | `0x8002a534` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c190` | `0x8002c688` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c688` | `0x8002d2ac` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d2ac` | `0x8002d87c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d87c` | `0x8002f23c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f23c` | `0x8002f260` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f260` | `0x8002f27c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f27c` | `0x8002f540` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f540` | `0x8002f550` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f550` | `0x8002f584` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f584` | `0x8002f59c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f59c` | `0x8002f5ac` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f5ac` | `0x8002f5e0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f5e0` | `0x8002f5e8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f5e8` | `0x8002f694` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f694` | `0x8002f6a0` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f6a0` | `0x8002f6c8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f6c8` | `0x8002f708` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f708` | `0x8002f738` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f738` | `0x8002f738` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f738` | `0x8002f750` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f750` | `0x8002f758` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f758` | `0x8002f764` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f764` | `0x8002f77c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f77c` | `0x8002f794` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f794` | `0x8002f7a8` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f7a8` | `0x8002f7c8` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f7c8` | `0x8002f7dc` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f7dc` | `0x8002f808` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f808` | `0x8002f850` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f850` | `0x8002f930` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f930` | `0x8002f9e0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f9e0` | `0x8002fa00` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fa00` | `0x8002fa74` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fa74` | `0x8002fa84` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fa84` | `0x8002fa90` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fa90` | `0x8002fb74` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fb74` | `0x8002fb9c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fb9c` | `0x8002fbb0` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fbb0` | `0x8002fbb0` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fbb0` | `0x8002fbb0` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fbb0` | `0x8002fbd0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fbd0` | `0x8002fc00` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fc00` | `0x8002fc24` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fc24` | `0x8002fc44` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fc44` | `0x8002fc48` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fc48` | `0x8002fcd4` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fcd4` | `0x8002fce4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fce4` | `0x8002fcf4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fcf4` | `0x8002fe24` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fe24` | `0x8002fe24` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fe24` | `0x8002ffc0` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002ffc0` | `0x8002ffc0` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002ffc0` | `0x80030020` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030dd8` | `0x80030e00` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030e00` | `0x80031010` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031110` | `0x800311bc` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800311bc` | `0x80031240` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031240` | `0x800312c0` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800312c0` | `0x80031378` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031378` | `0x800313ec` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800313ec` | `0x800315b0` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800315b0` | `0x80031620` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031620` | `0x80031698` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031698` | `0x80031848` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031848` | `0x800318c4` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x800318c4` | `0x80031914` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031914` | `0x80031964` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031964` | `0x80031994` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031994` | `0x800319d8` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800319d8` | `0x80031a1c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031a1c` | `0x80031acc` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031acc` | `0x80031c28` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031c28` | `0x80031f24` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031f24` | `0x80032100` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032100` | `0x800321ac` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800321ac` | `0x80032324` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032324` | `0x800324f0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800324f0` | `0x80032624` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032714` | `0x800327f0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800327f0` | `0x80032940` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032940` | `0x80032b1c` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032ccc` | `0x80032eb8` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032eb8` | `0x80032f0c` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032f0c` | `0x80032f54` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032f54` | `0x80033028` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033028` | `0x80033108` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033108` | `0x800332c0` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033cd8` | `0x80033d54` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033d54` | `0x80033e40` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800344a4` | `0x80034514` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034514` | `0x80034574` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034950` | `0x800349a4` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034b6c` | `0x80034dd8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034dd8` | `0x80035118` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035118` | `0x800353c8` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800353c8` | `0x800356fc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800356fc` | `0x80035a84` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035a84` | `0x80035ba4` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035bc4` | `0x80035ff4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035ff4` | `0x80036438` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003648c` | `0x80036638` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036aac` | `0x80036c70` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037400` | `0x800376d8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037fc4` | `0x80038054` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038054` | `0x80038124` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800382fc` | `0x80038358` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038548` | `0x800387b4` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x800387b4` | `0x80038ad4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038ad4` | `0x80038d84` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038d84` | `0x80038f60` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038f60` | `0x800392a8` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800393f4` | `0x8003ac58` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ac58` | `0x8003be94` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003bfb8` | `0x8003c0d4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c0e4` | `0x8003c114` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c114` | `0x8003c6b0` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c6b0` | `0x8003c9c0` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c9c0` | `0x8003c9c8` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c9c8` | `0x8003c9cc` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c9cc` | `0x8003cbb0` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cca8` | `0x8003cef0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cef0` | `0x8003d554` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d554` | `0x8003d670` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d670` | `0x8003d888` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d888` | `0x8003d8c8` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d8c8` | `0x8003d910` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d910` | `0x8003d960` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d960` | `0x8003d9b8` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d9b8` | `0x8003da18` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003da18` | `0x8003da80` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003da80` | `0x8003daf0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003daf0` | `0x8003db68` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003db68` | `0x8003dbe8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dbe8` | `0x8003dc70` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dc70` | `0x8003dd00` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dd00` | `0x8003dd98` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003dd98` | `0x8003de38` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003de38` | `0x8003dee0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003dee0` | `0x8003df90` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003df90` | `0x8003e048` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e048` | `0x8003e108` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e108` | `0x8003e1d0` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e1d0` | `0x8003e2a0` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e2a0` | `0x8003e378` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e378` | `0x8003e458` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e458` | `0x8003e540` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e540` | `0x8003e630` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e630` | `0x8003e728` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e728` | `0x8003e828` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e828` | `0x8003e930` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e930` | `0x8003ea40` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ea40` | `0x8003eb58` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003eb58` | `0x8003ec78` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ec78` | `0x8003eda0` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003eda0` | `0x8003eed0` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003eed0` | `0x8003f008` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f008` | `0x8003f148` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f148` | `0x8003f1c0` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f1c0` | `0x8003f238` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f238` | `0x8003f2b0` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f2b0` | `0x8003f328` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f328` | `0x8003f3a0` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f3a0` | `0x8003f418` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f418` | `0x8003f490` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f490` | `0x8003f508` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f508` | `0x8003f580` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f580` | `0x8003f5f8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f5f8` | `0x8003f670` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f670` | `0x8003f6e8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f6e8` | `0x8003f760` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f760` | `0x8003f7d8` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f7d8` | `0x8003f850` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f850` | `0x8003f8c8` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f8c8` | `0x8003f938` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f938` | `0x8003f9a8` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f9a8` | `0x8003fa18` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fa18` | `0x8003fa88` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fa88` | `0x8003faf8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003faf8` | `0x8003fb68` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fb68` | `0x8003fbd8` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fbd8` | `0x8003fc48` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fc48` | `0x8003fcb8` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fcb8` | `0x8003fd28` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fd28` | `0x8003fd98` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fd98` | `0x8003fe08` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fe08` | `0x8003fe78` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003fe78` | `0x8003fee8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003fee8` | `0x8003ff58` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003ff58` | `0x8003ffc8` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003ffc8` | `0x8003ffe0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003ffe0` | `0x8003fff4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003fff4` | `0x80040080` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040080` | `0x80040098` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040098` | `0x800400ac` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800400ac` | `0x80040134` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040134` | `0x8004014c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8004014c` | `0x80040160` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040160` | `0x80040180` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040180` | `0x80040188` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040188` | `0x80040194` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040194` | `0x80040198` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040198` | `0x8004021c` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8004021c` | `0x800402c4` | 168 | `h_ADD` | UNCONVERTED |
| `0x800402c4` | `0x800403f8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800403f8` | `0x800404a0` | 168 | `h_SUB` | UNCONVERTED |
| `0x800404a0` | `0x80040598` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040598` | `0x80040630` | 152 | `h_LT` | UNCONVERTED |
| `0x80040630` | `0x800406c8` | 152 | `h_GT` | UNCONVERTED |
| `0x800406c8` | `0x8004075c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004075c` | `0x800407f0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800407f0` | `0x80040874` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040874` | `0x800408d4` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800408d4` | `0x80040948` | 116 | `h_AND` | UNCONVERTED |
| `0x80040948` | `0x800409bc` | 116 | `h_OR` | UNCONVERTED |
| `0x800409bc` | `0x80040a30` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040a30` | `0x80040a90` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040a90` | `0x80040b7c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040b7c` | `0x80040d1c` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040d1c` | `0x80040ebc` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040ebc` | `0x80041070` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041070` | `0x80041170` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041170` | `0x800411a4` | 52 | `h_POP` | UNCONVERTED |
| `0x800411a4` | `0x800414f0` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800414f0` | `0x800417d0` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x800417d0` | `0x800418f0` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800418f0` | `0x80041934` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041934` | `0x80041978` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041978` | `0x800419c8` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x800419c8` | `0x80041a18` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041a18` | `0x80041a68` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041a68` | `0x80041ab8` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041ab8` | `0x80041b08` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041b08` | `0x80041b58` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041b58` | `0x80041ba8` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041ba8` | `0x80041bf8` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041bf8` | `0x80041c48` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041c48` | `0x80041c98` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041c98` | `0x80041ce8` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041ce8` | `0x80041d38` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041d38` | `0x80041d88` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041d88` | `0x80041dd8` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041dd8` | `0x80041e28` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041e28` | `0x80041ec0` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041ec0` | `0x80041fac` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041fac` | `0x80041ff0` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041ff0` | `0x8004220c` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x8004220c` | `0x800423dc` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800423dc` | `0x80042420` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042420` | `0x800425ec` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800425ec` | `0x800425f4` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800425f4` | `0x800426b4` | 192 | `h_JUMP` | UNCONVERTED |
| `0x800426b4` | `0x800427a8` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x800427a8` | `0x800427ec` | 68 | `h_PC` | UNCONVERTED |
| `0x800427ec` | `0x80042a74` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042a74` | `0x80042d68` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042d68` | `0x8004307c` | 788 | `h_LOG1` | UNCONVERTED |
| `0x8004307c` | `0x800433b0` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800433b0` | `0x80043704` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043704` | `0x80043a78` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043a78` | `0x80043d20` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043d20` | `0x80044028` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044028` | `0x80044694` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044694` | `0x80044c3c` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044c3c` | `0x800451bc` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800451bc` | `0x80045a48` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045a48` | `0x80045b34` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045b34` | `0x80045c04` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045c04` | `0x80045e84` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80045e84` | `0x8004681c` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x8004681c` | `0x80046e00` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80046e00` | `0x80046e1c` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046e1c` | `0x80048340` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048340` | `0x8004838c` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x8004838c` | `0x80048530` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048530` | `0x800492f8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800492f8` | `0x8004b5a4` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b5a4` | `0x8004c71c` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c71c` | `0x8004d380` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d380` | `0x8004e188` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e188` | `0x8004edec` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004edec` | `0x8004f6a4` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f6a4` | `0x8004ff98` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004ff98` | `0x80050534` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050534` | `0x80050be0` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050be0` | `0x80050c00` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050c00` | `0x800512ac` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800512ac` | `0x800512cc` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800512cc` | `0x80051bfc` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051bfc` | `0x80051f48` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051f48` | `0x800520b8` | 368 | `h_STOP` | UNCONVERTED |
| `0x800520b8` | `0x800520bc` | 4 | `h_invalid` | UNCONVERTED |
| `0x800520bc` | `0x80052144` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80052144` | `0x80052338` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052338` | `0x80052368` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052368` | `0x8005237c` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x8005237c` | `0x8005238c` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x8005238c` | `0x800523bc` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800523bc` | `0x800525b0` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x800525b0` | `0x800525e0` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800525e0` | `0x800525f4` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800525f4` | `0x80052604` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052604` | `0x80052634` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052634` | `0x80052658` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052658` | `0x80052688` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052688` | `0x8005287c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x8005287c` | `0x800528ac` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x800528ac` | `0x800528c0` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x800528c0` | `0x800528d0` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x800528d0` | `0x80052900` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052900` | `0x80052af4` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052af4` | `0x80052b24` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052b24` | `0x80052b38` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052b38` | `0x80052b48` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052b48` | `0x80052b78` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052b78` | `0x80052d6c` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052d6c` | `0x80052d9c` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052d9c` | `0x80052db0` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052db0` | `0x80052dc0` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052dc0` | `0x80052df0` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052df0` | `0x80052df0` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052df0` | `0x80052e0c` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052f98` | `0x800531cc` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800536cc` | `0x800537fc` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800537fc` | `0x80053858` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053858` | `0x80053878` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053878` | `0x800539b4` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053b84` | `0x80053b90` | 12 | `requests_hash_verify` | TAIL |
