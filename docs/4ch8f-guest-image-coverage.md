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
not linked** (102 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053d98), 343448 bytes (`RegionMap.textSizeBytes = 0x53d98`)

- symbols in `.text`: 907 (443 converted, 464 unconverted)
- covered by converted `_prog`s: 119816 bytes (34.89%)
- NOT covered: 223632 bytes (65.11%), 465 ranges

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
| `0x8000df64` | `0x8000f280` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f6b0` | `0x8000f890` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f890` | `0x8000f974` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f974` | `0x8000fa50` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fa50` | `0x8000fae4` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fae4` | `0x8000fba0` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fba0` | `0x8000fc50` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fc50` | `0x8000fd34` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000fd34` | `0x8000fd70` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000fd70` | `0x8000fea0` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000fea0` | `0x8000ffc4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000ffc4` | `0x80010074` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010074` | `0x800101f0` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800101f0` | `0x800102c8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800102c8` | `0x80010458` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010458` | `0x800105f4` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800105f4` | `0x800106a4` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800106a4` | `0x8001070c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8001070c` | `0x800107a8` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800107a8` | `0x80010ddc` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010ddc` | `0x800110c4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800110c4` | `0x8001141c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001141c` | `0x800118f8` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x800118f8` | `0x80011b9c` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011b9c` | `0x80011cb8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011cb8` | `0x80011f70` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011f70` | `0x80012190` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012190` | `0x80012528` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012528` | `0x8001263c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001263c` | `0x8001265c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001265c` | `0x800128e4` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x800128e4` | `0x800129c8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800129c8` | `0x80012a70` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012a70` | `0x800131a4` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800131a4` | `0x800137dc` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013b18` | `0x80013b2c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013b2c` | `0x80013b38` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013b38` | `0x80013b88` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013b88` | `0x80013ba8` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013ba8` | `0x80013c0c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013c0c` | `0x80013eb4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013eb4` | `0x80014108` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014108` | `0x800142bc` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80014ebc` | `0x800150b4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800153d4` | `0x80015604` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x800159f4` | `0x800184f0` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800184f0` | `0x80019284` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019284` | `0x800194a0` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019788` | `0x8001981c` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a014` | `0x8001a26c` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a26c` | `0x8001a4e4` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a4e4` | `0x8001a778` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001ad74` | `0x8001b090` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b458` | `0x8001b6d0` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b6d0` | `0x8001b974` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b974` | `0x8001c438` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c74c` | `0x8001c794` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001ce24` | `0x8001d00c` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d00c` | `0x8001d068` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d068` | `0x8001d134` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d134` | `0x8001d208` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d208` | `0x8001e198` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ea6c` | `0x8001eb80` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001eb80` | `0x8001efb4` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fc68` | `0x8001fca8` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff08` | `0x80020050` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020050` | `0x80020080` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x800205d0` | `0x80020760` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021954` | `0x80021a70` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021a70` | `0x80021c34` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c34` | `0x80021ec4` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022598` | `0x800226b8` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800233d4` | `0x800233f0` | 28 | `keccak_init` | UNCONVERTED |
| `0x800233f0` | `0x80023464` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023464` | `0x800234b4` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234b4` | `0x800234e0` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800234e0` | `0x800235c0` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800235c0` | `0x80023640` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023640` | `0x80023670` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237b0` | `0x80023874` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023874` | `0x800238c8` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800238c8` | `0x800238f8` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800238f8` | `0x80023938` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023938` | `0x80023970` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023970` | `0x800239b0` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b10` | `0x80023b28` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024ae8` | `0x80024ce4` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024d7c` | `0x80024e88` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024eec` | `0x800250b4` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250b4` | `0x8002539c` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x8002539c` | `0x80025484` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025484` | `0x80025560` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025560` | `0x80025638` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259ec` | `0x80025b10` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025b10` | `0x80025c08` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026430` | `0x80026440` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026624` | `0x8002683c` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x8002683c` | `0x80026a30` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026dc4` | `0x80027448` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028364` | `0x80028880` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288e0` | `0x80028980` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800295cc` | `0x80029dc0` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a454` | `0x8002a6f0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a6f0` | `0x8002a728` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c384` | `0x8002c87c` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c87c` | `0x8002d4a0` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d4a0` | `0x8002da70` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002da70` | `0x8002f430` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f430` | `0x8002f454` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f454` | `0x8002f470` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f470` | `0x8002f734` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f734` | `0x8002f744` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f744` | `0x8002f778` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f778` | `0x8002f790` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f790` | `0x8002f7a0` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f7a0` | `0x8002f7d4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f7d4` | `0x8002f7dc` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f7dc` | `0x8002f888` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f888` | `0x8002f894` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f894` | `0x8002f8bc` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f8bc` | `0x8002f8fc` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f8fc` | `0x8002f92c` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f92c` | `0x8002f92c` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f92c` | `0x8002f944` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f944` | `0x8002f94c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f94c` | `0x8002f958` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f958` | `0x8002f970` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f970` | `0x8002f988` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f988` | `0x8002f99c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f99c` | `0x8002f9bc` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f9bc` | `0x8002f9d0` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f9d0` | `0x8002f9fc` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f9fc` | `0x8002fa44` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fa44` | `0x8002fb24` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fb24` | `0x8002fbd4` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fbd4` | `0x8002fbf4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fbf4` | `0x8002fc68` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc78` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fc78` | `0x8002fc84` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fc84` | `0x8002fd68` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fd68` | `0x8002fd90` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fd90` | `0x8002fda4` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fda4` | `0x8002fda4` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fda4` | `0x8002fda4` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fda4` | `0x8002fdc4` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fdc4` | `0x8002fdf4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fdf4` | `0x8002fe18` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fe18` | `0x8002fe38` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe3c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fe3c` | `0x8002fedc` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fedc` | `0x8002feec` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002feec` | `0x8002fefc` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fefc` | `0x8003002c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8003002c` | `0x8003002c` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8003002c` | `0x800301c8` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800301c8` | `0x800301c8` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800301c8` | `0x80030228` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030fe0` | `0x80031008` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031008` | `0x80031218` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031318` | `0x800313c4` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800313c4` | `0x80031448` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031448` | `0x800314c8` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800314c8` | `0x80031580` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031580` | `0x800315f4` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800315f4` | `0x800317b8` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800317b8` | `0x80031828` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031828` | `0x800318a0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x800318a0` | `0x80031a50` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031a50` | `0x80031acc` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031acc` | `0x80031b1c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031b1c` | `0x80031b6c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031b6c` | `0x80031b9c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031b9c` | `0x80031be0` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031be0` | `0x80031c24` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031c24` | `0x80031cd4` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031cd4` | `0x80031e30` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031e30` | `0x8003212c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003212c` | `0x80032308` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032308` | `0x800323b4` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800323b4` | `0x8003252c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x8003252c` | `0x800326f8` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800326f8` | `0x8003282c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x8003291c` | `0x800329f8` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800329f8` | `0x80032b48` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032b48` | `0x80032d24` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032ed4` | `0x800330c0` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800330c0` | `0x80033114` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033114` | `0x8003315c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8003315c` | `0x80033230` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033230` | `0x80033310` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033310` | `0x800334c8` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033ee0` | `0x80033f5c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033f5c` | `0x80034048` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800346ac` | `0x8003471c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x8003471c` | `0x8003477c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034b58` | `0x80034bac` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034d74` | `0x80034fe0` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034fe0` | `0x80035320` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035320` | `0x800355d0` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800355d0` | `0x80035904` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035904` | `0x80035c8c` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035c8c` | `0x80035dac` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035dcc` | `0x800361fc` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800361fc` | `0x80036640` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036694` | `0x80036840` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036cb4` | `0x80036e78` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037608` | `0x800378e0` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800381cc` | `0x8003825c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003825c` | `0x8003832c` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038504` | `0x80038560` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038750` | `0x800389bc` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x800389bc` | `0x80038cdc` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038cdc` | `0x80038f8c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038f8c` | `0x80039168` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039168` | `0x800394b0` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800395fc` | `0x8003ae60` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ae60` | `0x8003c09c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c1c0` | `0x8003c2dc` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c2ec` | `0x8003c31c` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c31c` | `0x8003c8b8` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c8b8` | `0x8003cbc8` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cbc8` | `0x8003cbd0` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cbd0` | `0x8003cbd4` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cbd4` | `0x8003cdb8` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003ceb0` | `0x8003d0f8` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d0f8` | `0x8003d75c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d75c` | `0x8003d878` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d878` | `0x8003da90` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003da90` | `0x8003dad0` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003dad0` | `0x8003db18` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003db18` | `0x8003db68` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003db68` | `0x8003dbc0` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dbc0` | `0x8003dc20` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dc20` | `0x8003dc88` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dc88` | `0x8003dcf8` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dcf8` | `0x8003dd70` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dd70` | `0x8003ddf0` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003ddf0` | `0x8003de78` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003de78` | `0x8003df08` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003df08` | `0x8003dfa0` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003dfa0` | `0x8003e040` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e040` | `0x8003e0e8` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e0e8` | `0x8003e198` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e198` | `0x8003e250` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e250` | `0x8003e310` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e310` | `0x8003e3d8` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e3d8` | `0x8003e4a8` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e4a8` | `0x8003e580` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e580` | `0x8003e660` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e660` | `0x8003e748` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e748` | `0x8003e838` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e838` | `0x8003e930` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e930` | `0x8003ea30` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ea30` | `0x8003eb38` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003eb38` | `0x8003ec48` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ec48` | `0x8003ed60` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ed60` | `0x8003ee80` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ee80` | `0x8003efa8` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003efa8` | `0x8003f0d8` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f0d8` | `0x8003f210` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f210` | `0x8003f350` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f350` | `0x8003f3c8` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f3c8` | `0x8003f440` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f440` | `0x8003f4b8` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f4b8` | `0x8003f530` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f530` | `0x8003f5a8` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f5a8` | `0x8003f620` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f620` | `0x8003f698` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f698` | `0x8003f710` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f710` | `0x8003f788` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f788` | `0x8003f800` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f800` | `0x8003f878` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f878` | `0x8003f8f0` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f8f0` | `0x8003f968` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f968` | `0x8003f9e0` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f9e0` | `0x8003fa58` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fa58` | `0x8003fad0` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fad0` | `0x8003fb40` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fb40` | `0x8003fbb0` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fbb0` | `0x8003fc20` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fc20` | `0x8003fc90` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fc90` | `0x8003fd00` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fd00` | `0x8003fd70` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fd70` | `0x8003fde0` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fde0` | `0x8003fe50` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fe50` | `0x8003fec0` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fec0` | `0x8003ff30` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003ff30` | `0x8003ffa0` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003ffa0` | `0x80040010` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040010` | `0x80040080` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040080` | `0x800400f0` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800400f0` | `0x80040160` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040160` | `0x800401d0` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800401d0` | `0x800401e8` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800401e8` | `0x800401fc` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800401fc` | `0x80040288` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040288` | `0x800402a0` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800402a0` | `0x800402b4` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800402b4` | `0x8004033c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8004033c` | `0x80040354` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040354` | `0x80040368` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040368` | `0x80040388` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040388` | `0x80040390` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040390` | `0x8004039c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8004039c` | `0x800403a0` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800403a0` | `0x80040424` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040424` | `0x800404cc` | 168 | `h_ADD` | UNCONVERTED |
| `0x800404cc` | `0x80040600` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040600` | `0x800406a8` | 168 | `h_SUB` | UNCONVERTED |
| `0x800406a8` | `0x800407a0` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x800407a0` | `0x80040838` | 152 | `h_LT` | UNCONVERTED |
| `0x80040838` | `0x800408d0` | 152 | `h_GT` | UNCONVERTED |
| `0x800408d0` | `0x80040964` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040964` | `0x800409f8` | 148 | `h_SGT` | UNCONVERTED |
| `0x800409f8` | `0x80040a7c` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040a7c` | `0x80040adc` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040adc` | `0x80040b50` | 116 | `h_AND` | UNCONVERTED |
| `0x80040b50` | `0x80040bc4` | 116 | `h_OR` | UNCONVERTED |
| `0x80040bc4` | `0x80040c38` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040c38` | `0x80040c98` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040c98` | `0x80040d84` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040d84` | `0x80040f24` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040f24` | `0x800410c4` | 416 | `h_SHR` | UNCONVERTED |
| `0x800410c4` | `0x80041278` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041278` | `0x80041378` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041378` | `0x800413ac` | 52 | `h_POP` | UNCONVERTED |
| `0x800413ac` | `0x800416f8` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800416f8` | `0x800419d8` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x800419d8` | `0x80041af8` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041af8` | `0x80041b3c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041b3c` | `0x80041b80` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041b80` | `0x80041bd0` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041bd0` | `0x80041c20` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041c20` | `0x80041c70` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041c70` | `0x80041cc0` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041cc0` | `0x80041d10` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041d10` | `0x80041d60` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041d60` | `0x80041db0` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041db0` | `0x80041e00` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041e00` | `0x80041e50` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041e50` | `0x80041ea0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041ea0` | `0x80041ef0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041ef0` | `0x80041f40` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041f40` | `0x80041f90` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041f90` | `0x80041fe0` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041fe0` | `0x80042030` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042030` | `0x800420c8` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800420c8` | `0x800421b4` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800421b4` | `0x800421f8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800421f8` | `0x80042414` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042414` | `0x800425e4` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800425e4` | `0x80042628` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042628` | `0x800427f4` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800427f4` | `0x800427fc` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800427fc` | `0x800428bc` | 192 | `h_JUMP` | UNCONVERTED |
| `0x800428bc` | `0x800429b0` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x800429b0` | `0x800429f4` | 68 | `h_PC` | UNCONVERTED |
| `0x800429f4` | `0x80042c7c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042c7c` | `0x80042f70` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042f70` | `0x80043284` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043284` | `0x800435b8` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800435b8` | `0x8004390c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x8004390c` | `0x80043c80` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043c80` | `0x80043f28` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043f28` | `0x80044230` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044230` | `0x8004489c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004489c` | `0x80044e44` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044e44` | `0x800453c4` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800453c4` | `0x80045c50` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045c50` | `0x80045d3c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045d3c` | `0x80045e0c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045e0c` | `0x8004608c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x8004608c` | `0x80046a24` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046a24` | `0x80047008` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047008` | `0x80047024` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047024` | `0x80048548` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048548` | `0x80048594` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048594` | `0x80048738` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048738` | `0x80049500` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049500` | `0x8004b7ac` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b7ac` | `0x8004c924` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c924` | `0x8004d588` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d588` | `0x8004e390` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e390` | `0x8004eff4` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004eff4` | `0x8004f8ac` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f8ac` | `0x800501a0` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800501a0` | `0x8005073c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8005073c` | `0x80050de8` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050de8` | `0x80050e08` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050e08` | `0x800514b4` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800514b4` | `0x800514d4` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800514d4` | `0x80051e04` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051e04` | `0x80052150` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052150` | `0x800522c0` | 368 | `h_STOP` | UNCONVERTED |
| `0x800522c0` | `0x800522c4` | 4 | `h_invalid` | UNCONVERTED |
| `0x800522c4` | `0x8005234c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005234c` | `0x80052540` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052540` | `0x80052570` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052570` | `0x80052584` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052584` | `0x80052594` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052594` | `0x800525c4` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800525c4` | `0x800527b8` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x800527b8` | `0x800527e8` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800527e8` | `0x800527fc` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800527fc` | `0x8005280c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x8005280c` | `0x8005283c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x8005283c` | `0x80052860` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052860` | `0x80052890` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052890` | `0x80052a84` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052a84` | `0x80052ab4` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052ab4` | `0x80052ac8` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052ac8` | `0x80052ad8` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052ad8` | `0x80052b08` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052b08` | `0x80052cfc` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052cfc` | `0x80052d2c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052d2c` | `0x80052d40` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052d40` | `0x80052d50` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052d50` | `0x80052d80` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052d80` | `0x80052f74` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052f74` | `0x80052fa4` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052fa4` | `0x80052fb8` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052fb8` | `0x80052fc8` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052fc8` | `0x80052ff8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052ff8` | `0x80052ff8` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052ff8` | `0x80053014` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800531a0` | `0x800533d4` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800538d4` | `0x80053a04` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053a04` | `0x80053a60` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053a60` | `0x80053a80` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053a80` | `0x80053bbc` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053d8c` | `0x80053d98` | 12 | `requests_hash_verify` | TAIL |
