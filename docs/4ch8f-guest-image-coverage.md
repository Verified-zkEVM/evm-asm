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
not linked** (99 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053960), 342368 bytes (`RegionMap.textSizeBytes = 0x53960`)

- symbols in `.text`: 903 (446 converted, 457 unconverted)
- covered by converted `_prog`s: 120392 bytes (35.16%)
- NOT covered: 221976 bytes (64.84%), 458 ranges

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
| `0x8000dc98` | `0x8000efb4` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f3e4` | `0x8000f5c4` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f5c4` | `0x8000f6a8` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f6a8` | `0x8000f784` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f784` | `0x8000f818` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f818` | `0x8000f8d4` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000f8d4` | `0x8000f984` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000f984` | `0x8000fa68` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000fa68` | `0x8000faa4` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000faa4` | `0x8000fbd4` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000fbd4` | `0x8000fcf8` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000fcf8` | `0x8000fda8` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000fda8` | `0x8000ff24` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8000ff24` | `0x8000fffc` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8000fffc` | `0x8001018c` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8001018c` | `0x80010328` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010328` | `0x800103d8` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800103d8` | `0x80010440` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010440` | `0x800104dc` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800104dc` | `0x80010b10` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010b10` | `0x80010df8` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010df8` | `0x80011150` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011150` | `0x8001162c` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x8001162c` | `0x800118d0` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800118d0` | `0x800119ec` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800119ec` | `0x80011ca4` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011ca4` | `0x80011ec4` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80011ec4` | `0x8001225c` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x8001225c` | `0x80012370` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012370` | `0x80012390` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012390` | `0x80012618` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012618` | `0x800126fc` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800126fc` | `0x800127a4` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800127a4` | `0x80012ed8` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80012ed8` | `0x80013510` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001384c` | `0x80013860` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013860` | `0x8001386c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x8001386c` | `0x800138bc` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800138bc` | `0x800138dc` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800138dc` | `0x80013940` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013940` | `0x80013be8` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013be8` | `0x80013e3c` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80013e3c` | `0x80013ff0` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80014bf0` | `0x80014de8` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015108` | `0x80015338` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015728` | `0x80018224` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80018224` | `0x80018fb8` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80018fb8` | `0x800191d4` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800194bc` | `0x80019550` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019d48` | `0x80019fa0` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x80019fa0` | `0x8001a218` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a218` | `0x8001a4ac` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001aaa8` | `0x8001adc4` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b18c` | `0x8001b404` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b404` | `0x8001b6a8` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b6a8` | `0x8001c16c` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c480` | `0x8001c4c8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001cb58` | `0x8001cd40` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001cd40` | `0x8001cd9c` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001cd9c` | `0x8001ce68` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001ce68` | `0x8001cf3c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cf3c` | `0x8001debc` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e790` | `0x8001e8a4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e8a4` | `0x8001ebac` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f860` | `0x8001f8a0` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fb00` | `0x8001fc48` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001fc48` | `0x8001fc78` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x800201c8` | `0x80020358` | 400 | `destroy_storage` | UNCONVERTED |
| `0x8002154c` | `0x80021668` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021668` | `0x8002182c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x8002182c` | `0x80021abc` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022190` | `0x800222b0` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022fb0` | `0x80022fcc` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022fcc` | `0x80023040` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023040` | `0x80023090` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023090` | `0x800230bc` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800230bc` | `0x8002319c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x8002319c` | `0x8002321c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x8002321c` | `0x8002324c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x8002338c` | `0x80023450` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023450` | `0x800234a4` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800234a4` | `0x800234d4` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800234d4` | `0x80023514` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023514` | `0x8002354c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002354c` | `0x8002358c` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800236ec` | `0x80023704` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800246c4` | `0x800248c0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024958` | `0x80024a64` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024ac8` | `0x80024c90` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024c90` | `0x80024f78` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024f78` | `0x80025060` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025060` | `0x8002513c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x8002513c` | `0x80025214` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800255c8` | `0x800256ec` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800256ec` | `0x800257e4` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x8002600c` | `0x8002601c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026200` | `0x80026418` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026418` | `0x8002660c` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800269a0` | `0x80027024` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027f40` | `0x8002845c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800284bc` | `0x8002855c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800291a8` | `0x8002999c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a030` | `0x8002a2cc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a2cc` | `0x8002a304` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002bf60` | `0x8002c458` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c458` | `0x8002d07c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d07c` | `0x8002d64c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d64c` | `0x8002f00c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f00c` | `0x8002f030` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f030` | `0x8002f04c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f04c` | `0x8002f310` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f310` | `0x8002f320` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f320` | `0x8002f354` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f354` | `0x8002f36c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f36c` | `0x8002f37c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f37c` | `0x8002f3b0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f3b0` | `0x8002f3b8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f3b8` | `0x8002f464` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f464` | `0x8002f470` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f470` | `0x8002f498` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f498` | `0x8002f4d8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f4d8` | `0x8002f508` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f508` | `0x8002f508` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f508` | `0x8002f520` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f520` | `0x8002f528` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f528` | `0x8002f534` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f534` | `0x8002f54c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f54c` | `0x8002f564` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f564` | `0x8002f578` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f578` | `0x8002f598` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f598` | `0x8002f5ac` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f5ac` | `0x8002f5d8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f5d8` | `0x8002f620` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f620` | `0x8002f700` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f700` | `0x8002f7b0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f7b0` | `0x8002f7d0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f7d0` | `0x8002f844` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f844` | `0x8002f854` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f854` | `0x8002f860` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f860` | `0x8002f944` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f944` | `0x8002f96c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f96c` | `0x8002f980` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f980` | `0x8002f980` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f980` | `0x8002f980` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f980` | `0x8002f9a0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f9a0` | `0x8002f9d0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f9d0` | `0x8002f9f4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f9f4` | `0x8002fa14` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fa14` | `0x8002fa18` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fa18` | `0x8002faa4` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002faa4` | `0x8002fab4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fab4` | `0x8002fac4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fac4` | `0x8002fbf4` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fbf4` | `0x8002fbf4` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fbf4` | `0x8002fd90` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002fd90` | `0x8002fd90` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002fd90` | `0x8002fdf0` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030ba8` | `0x80030bd0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030bd0` | `0x80030de0` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030ee0` | `0x80030f8c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030f8c` | `0x80031010` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031010` | `0x80031090` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031090` | `0x80031148` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031148` | `0x800311bc` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800311bc` | `0x80031380` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031380` | `0x800313f0` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800313f0` | `0x80031468` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031468` | `0x80031618` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031618` | `0x80031694` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031694` | `0x800316e4` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800316e4` | `0x80031734` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031734` | `0x80031764` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031764` | `0x800317a8` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800317a8` | `0x800317ec` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800317ec` | `0x8003189c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8003189c` | `0x800319f8` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800319f8` | `0x80031cf4` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031cf4` | `0x80031ed0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031ed0` | `0x80031f7c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031f7c` | `0x800320f4` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800320f4` | `0x800322c0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800322c0` | `0x800323f4` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800324e4` | `0x800325c0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800325c0` | `0x80032710` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032710` | `0x800328ec` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032a9c` | `0x80032c88` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032c88` | `0x80032cdc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032cdc` | `0x80032d24` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032d24` | `0x80032df8` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032df8` | `0x80032ed8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032ed8` | `0x80033090` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033aa8` | `0x80033b24` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033b24` | `0x80033c10` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034274` | `0x800342e4` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800342e4` | `0x80034344` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034720` | `0x80034774` | 84 | `bnq_sub` | UNCONVERTED |
| `0x8003493c` | `0x80034ba8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034ba8` | `0x80034ee8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034ee8` | `0x80035198` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035198` | `0x800354cc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800354cc` | `0x80035854` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035854` | `0x80035974` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035994` | `0x80035dc4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035dc4` | `0x80036208` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003625c` | `0x80036408` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x8003687c` | `0x80036a40` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800371d0` | `0x800374a8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037d94` | `0x80037e24` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037e24` | `0x80037ef4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800380cc` | `0x80038128` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038318` | `0x80038584` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038584` | `0x800388a4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x800388a4` | `0x80038b54` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038b54` | `0x80038d30` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038d30` | `0x80039078` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800391c4` | `0x8003aa28` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003aa28` | `0x8003bc64` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003bd88` | `0x8003bea4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003beb4` | `0x8003bee4` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003bee4` | `0x8003c480` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c480` | `0x8003c790` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c790` | `0x8003c798` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c798` | `0x8003c79c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c79c` | `0x8003c980` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003ca78` | `0x8003ccc0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003ccc0` | `0x8003d324` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d324` | `0x8003d440` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d440` | `0x8003d658` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d658` | `0x8003d698` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d698` | `0x8003d6e0` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d6e0` | `0x8003d730` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d730` | `0x8003d788` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d788` | `0x8003d7e8` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d7e8` | `0x8003d850` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d850` | `0x8003d8c0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d8c0` | `0x8003d938` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d938` | `0x8003d9b8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d9b8` | `0x8003da40` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003da40` | `0x8003dad0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dad0` | `0x8003db68` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003db68` | `0x8003dc08` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dc08` | `0x8003dcb0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003dcb0` | `0x8003dd60` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003dd60` | `0x8003de18` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003de18` | `0x8003ded8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003ded8` | `0x8003dfa0` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003dfa0` | `0x8003e070` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e070` | `0x8003e148` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e148` | `0x8003e228` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e228` | `0x8003e310` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e310` | `0x8003e400` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e400` | `0x8003e4f8` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e4f8` | `0x8003e5f8` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e5f8` | `0x8003e700` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e700` | `0x8003e810` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e810` | `0x8003e928` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e928` | `0x8003ea48` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ea48` | `0x8003eb70` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003eb70` | `0x8003eca0` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003eca0` | `0x8003edd8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003edd8` | `0x8003ef18` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003ef18` | `0x8003ef90` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ef90` | `0x8003f008` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f008` | `0x8003f080` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f080` | `0x8003f0f8` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f0f8` | `0x8003f170` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f170` | `0x8003f1e8` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f1e8` | `0x8003f260` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f260` | `0x8003f2d8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f2d8` | `0x8003f350` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f350` | `0x8003f3c8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f3c8` | `0x8003f440` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f440` | `0x8003f4b8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f4b8` | `0x8003f530` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f530` | `0x8003f5a8` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f5a8` | `0x8003f620` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f620` | `0x8003f698` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f698` | `0x8003f708` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f708` | `0x8003f778` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f778` | `0x8003f7e8` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f7e8` | `0x8003f858` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f858` | `0x8003f8c8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f8c8` | `0x8003f938` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f938` | `0x8003f9a8` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f9a8` | `0x8003fa18` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fa18` | `0x8003fa88` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fa88` | `0x8003faf8` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003faf8` | `0x8003fb68` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fb68` | `0x8003fbd8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fbd8` | `0x8003fc48` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003fc48` | `0x8003fcb8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003fcb8` | `0x8003fd28` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fd28` | `0x8003fd98` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003fd98` | `0x8003fdb0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003fdb0` | `0x8003fdc4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003fdc4` | `0x8003fe50` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003fe50` | `0x8003fe68` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003fe68` | `0x8003fe7c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003fe7c` | `0x8003ff04` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003ff04` | `0x8003ff1c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003ff1c` | `0x8003ff30` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003ff30` | `0x8003ff50` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003ff50` | `0x8003ff58` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003ff58` | `0x8003ff64` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003ff64` | `0x8003ff68` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003ff68` | `0x8003ffec` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003ffec` | `0x80040094` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040094` | `0x800401c8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800401c8` | `0x80040270` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040270` | `0x80040368` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040368` | `0x80040400` | 152 | `h_LT` | UNCONVERTED |
| `0x80040400` | `0x80040498` | 152 | `h_GT` | UNCONVERTED |
| `0x80040498` | `0x8004052c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004052c` | `0x800405c0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800405c0` | `0x80040644` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040644` | `0x800406a4` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800406a4` | `0x80040718` | 116 | `h_AND` | UNCONVERTED |
| `0x80040718` | `0x8004078c` | 116 | `h_OR` | UNCONVERTED |
| `0x8004078c` | `0x80040800` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040800` | `0x80040860` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040860` | `0x8004094c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x8004094c` | `0x80040aec` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040aec` | `0x80040c8c` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040c8c` | `0x80040e40` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040e40` | `0x80040f40` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040f40` | `0x80040f74` | 52 | `h_POP` | UNCONVERTED |
| `0x80040f74` | `0x800412c0` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800412c0` | `0x800415a0` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x800415a0` | `0x800416c0` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800416c0` | `0x80041704` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041704` | `0x80041748` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041748` | `0x80041798` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041798` | `0x800417e8` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800417e8` | `0x80041838` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041838` | `0x80041888` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041888` | `0x800418d8` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800418d8` | `0x80041928` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041928` | `0x80041978` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041978` | `0x800419c8` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800419c8` | `0x80041a18` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041a18` | `0x80041a68` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041a68` | `0x80041ab8` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041ab8` | `0x80041b08` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041b08` | `0x80041b58` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041b58` | `0x80041ba8` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041ba8` | `0x80041bf8` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041bf8` | `0x80041c90` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041c90` | `0x80041d7c` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041d7c` | `0x80041dc0` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041dc0` | `0x80041fdc` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041fdc` | `0x800421ac` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800421ac` | `0x800421f0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800421f0` | `0x800423bc` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800423bc` | `0x800423c4` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800423c4` | `0x80042484` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042484` | `0x80042578` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042578` | `0x800425bc` | 68 | `h_PC` | UNCONVERTED |
| `0x800425bc` | `0x80042844` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042844` | `0x80042b38` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042b38` | `0x80042e4c` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042e4c` | `0x80043180` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043180` | `0x800434d4` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800434d4` | `0x80043848` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043848` | `0x80043af0` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043af0` | `0x80043df8` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043df8` | `0x80044464` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044464` | `0x80044a0c` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044a0c` | `0x80044f8c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044f8c` | `0x80045818` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045818` | `0x80045904` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045904` | `0x800459d4` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800459d4` | `0x80045c54` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80045c54` | `0x800465ec` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800465ec` | `0x80046bd0` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80046bd0` | `0x80046bec` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046bec` | `0x80048110` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048110` | `0x8004815c` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x8004815c` | `0x80048300` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048300` | `0x800490c8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800490c8` | `0x8004b374` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b374` | `0x8004c4ec` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c4ec` | `0x8004d150` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d150` | `0x8004df58` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004df58` | `0x8004ebbc` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ebbc` | `0x8004f474` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f474` | `0x8004fd68` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004fd68` | `0x80050304` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050304` | `0x800509b0` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x800509b0` | `0x800509d0` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800509d0` | `0x8005107c` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x8005107c` | `0x8005109c` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x8005109c` | `0x800519cc` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800519cc` | `0x80051d18` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051d18` | `0x80051e88` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051e88` | `0x80051e8c` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051e8c` | `0x80051f14` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051f14` | `0x80052108` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052108` | `0x80052138` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052138` | `0x8005214c` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x8005214c` | `0x8005215c` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x8005215c` | `0x8005218c` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x8005218c` | `0x80052380` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052380` | `0x800523b0` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800523b0` | `0x800523c4` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800523c4` | `0x800523d4` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800523d4` | `0x80052404` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052404` | `0x80052428` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052428` | `0x80052458` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052458` | `0x8005264c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x8005264c` | `0x8005267c` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x8005267c` | `0x80052690` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052690` | `0x800526a0` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x800526a0` | `0x800526d0` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800526d0` | `0x800528c4` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800528c4` | `0x800528f4` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800528f4` | `0x80052908` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052908` | `0x80052918` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052918` | `0x80052948` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052948` | `0x80052b3c` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052b3c` | `0x80052b6c` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052b6c` | `0x80052b80` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052b80` | `0x80052b90` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052b90` | `0x80052bc0` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052bc0` | `0x80052bc0` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052bc0` | `0x80052bdc` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052d68` | `0x80052f9c` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x8005349c` | `0x800535cc` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800535cc` | `0x80053628` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053628` | `0x80053648` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053648` | `0x80053784` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053954` | `0x80053960` | 12 | `requests_hash_verify` | TAIL |
