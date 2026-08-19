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
not linked** (101 of 544 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053c48), 343112 bytes (`RegionMap.textSizeBytes = 0x53c48`)

- symbols in `.text`: 907 (443 converted, 464 unconverted)
- covered by converted `_prog`s: 119816 bytes (34.92%)
- NOT covered: 223296 bytes (65.08%), 465 ranges

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
| `0x8001d208` | `0x8001e188` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ea5c` | `0x8001eb70` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001eb70` | `0x8001ee78` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fb2c` | `0x8001fb6c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fdcc` | `0x8001ff14` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001ff14` | `0x8001ff44` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020494` | `0x80020624` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021818` | `0x80021934` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021934` | `0x80021af8` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021af8` | `0x80021d88` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x8002245c` | `0x8002257c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023298` | `0x800232b4` | 28 | `keccak_init` | UNCONVERTED |
| `0x800232b4` | `0x80023328` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023328` | `0x80023378` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023378` | `0x800233a4` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800233a4` | `0x80023484` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023484` | `0x80023504` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023504` | `0x80023534` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023674` | `0x80023738` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023738` | `0x8002378c` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x8002378c` | `0x800237bc` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800237bc` | `0x800237fc` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800237fc` | `0x80023834` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023834` | `0x80023874` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800239d4` | `0x800239ec` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800249ac` | `0x80024ba8` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024c40` | `0x80024d4c` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024db0` | `0x80024f78` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024f78` | `0x80025260` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025260` | `0x80025348` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025348` | `0x80025424` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025424` | `0x800254fc` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800258b0` | `0x800259d4` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800259d4` | `0x80025acc` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800262f4` | `0x80026304` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x800264e8` | `0x80026700` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026700` | `0x800268f4` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026c88` | `0x8002730c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028228` | `0x80028744` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800287a4` | `0x80028844` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029490` | `0x80029c84` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a318` | `0x8002a5b4` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a5b4` | `0x8002a5ec` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c248` | `0x8002c740` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c740` | `0x8002d364` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d364` | `0x8002d934` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d934` | `0x8002f2f4` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f2f4` | `0x8002f318` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f318` | `0x8002f334` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f334` | `0x8002f5f8` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f5f8` | `0x8002f608` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f608` | `0x8002f63c` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f63c` | `0x8002f654` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f654` | `0x8002f664` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f664` | `0x8002f698` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f698` | `0x8002f6a0` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f6a0` | `0x8002f74c` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f74c` | `0x8002f758` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f758` | `0x8002f780` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f780` | `0x8002f7c0` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f7c0` | `0x8002f7f0` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f7f0` | `0x8002f7f0` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f7f0` | `0x8002f808` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f808` | `0x8002f810` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f810` | `0x8002f81c` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f81c` | `0x8002f834` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f834` | `0x8002f84c` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f84c` | `0x8002f860` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f860` | `0x8002f880` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f880` | `0x8002f894` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f894` | `0x8002f8c0` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f8c0` | `0x8002f908` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f908` | `0x8002f9e8` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f9e8` | `0x8002fa98` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fa98` | `0x8002fab8` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fab8` | `0x8002fb2c` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fb2c` | `0x8002fb3c` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fb3c` | `0x8002fb48` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fb48` | `0x8002fc2c` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fc2c` | `0x8002fc54` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fc54` | `0x8002fc68` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc68` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc68` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc88` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fc88` | `0x8002fcb8` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fcb8` | `0x8002fcdc` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fcdc` | `0x8002fcfc` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fcfc` | `0x8002fd00` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fd00` | `0x8002fd8c` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fd8c` | `0x8002fd9c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fd9c` | `0x8002fdac` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fdac` | `0x8002fedc` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fedc` | `0x8002fedc` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fedc` | `0x80030078` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030078` | `0x80030078` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030078` | `0x800300d8` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030e90` | `0x80030eb8` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030eb8` | `0x800310c8` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800311c8` | `0x80031274` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031274` | `0x800312f8` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800312f8` | `0x80031378` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031378` | `0x80031430` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031430` | `0x800314a4` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800314a4` | `0x80031668` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031668` | `0x800316d8` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800316d8` | `0x80031750` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031750` | `0x80031900` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031900` | `0x8003197c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003197c` | `0x800319cc` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800319cc` | `0x80031a1c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031a1c` | `0x80031a4c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031a4c` | `0x80031a90` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031a90` | `0x80031ad4` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031ad4` | `0x80031b84` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031b84` | `0x80031ce0` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031ce0` | `0x80031fdc` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031fdc` | `0x800321b8` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800321b8` | `0x80032264` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032264` | `0x800323dc` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800323dc` | `0x800325a8` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800325a8` | `0x800326dc` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800327cc` | `0x800328a8` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800328a8` | `0x800329f8` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800329f8` | `0x80032bd4` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032d84` | `0x80032f70` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032f70` | `0x80032fc4` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032fc4` | `0x8003300c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8003300c` | `0x800330e0` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800330e0` | `0x800331c0` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800331c0` | `0x80033378` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033d90` | `0x80033e0c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033e0c` | `0x80033ef8` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x8003455c` | `0x800345cc` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800345cc` | `0x8003462c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034a08` | `0x80034a5c` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034c24` | `0x80034e90` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034e90` | `0x800351d0` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800351d0` | `0x80035480` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035480` | `0x800357b4` | 820 | `bng2_double` | UNCONVERTED |
| `0x800357b4` | `0x80035b3c` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035b3c` | `0x80035c5c` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035c7c` | `0x800360ac` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800360ac` | `0x800364f0` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036544` | `0x800366f0` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036b64` | `0x80036d28` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800374b8` | `0x80037790` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003807c` | `0x8003810c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003810c` | `0x800381dc` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800383b4` | `0x80038410` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038600` | `0x8003886c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003886c` | `0x80038b8c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038b8c` | `0x80038e3c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038e3c` | `0x80039018` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039018` | `0x80039360` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800394ac` | `0x8003ad10` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ad10` | `0x8003bf4c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c070` | `0x8003c18c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c19c` | `0x8003c1cc` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c1cc` | `0x8003c768` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c768` | `0x8003ca78` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ca78` | `0x8003ca80` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003ca80` | `0x8003ca84` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ca84` | `0x8003cc68` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cd60` | `0x8003cfa8` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cfa8` | `0x8003d60c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d60c` | `0x8003d728` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d728` | `0x8003d940` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d940` | `0x8003d980` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d980` | `0x8003d9c8` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d9c8` | `0x8003da18` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003da18` | `0x8003da70` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003da70` | `0x8003dad0` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dad0` | `0x8003db38` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003db38` | `0x8003dba8` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dba8` | `0x8003dc20` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dc20` | `0x8003dca0` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dca0` | `0x8003dd28` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dd28` | `0x8003ddb8` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003ddb8` | `0x8003de50` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003de50` | `0x8003def0` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003def0` | `0x8003df98` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003df98` | `0x8003e048` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e048` | `0x8003e100` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e100` | `0x8003e1c0` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e1c0` | `0x8003e288` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e288` | `0x8003e358` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e358` | `0x8003e430` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e430` | `0x8003e510` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e510` | `0x8003e5f8` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e5f8` | `0x8003e6e8` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e6e8` | `0x8003e7e0` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e7e0` | `0x8003e8e0` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e8e0` | `0x8003e9e8` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e9e8` | `0x8003eaf8` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003eaf8` | `0x8003ec10` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ec10` | `0x8003ed30` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ed30` | `0x8003ee58` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ee58` | `0x8003ef88` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003ef88` | `0x8003f0c0` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f0c0` | `0x8003f200` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f200` | `0x8003f278` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f278` | `0x8003f2f0` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f2f0` | `0x8003f368` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f368` | `0x8003f3e0` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f3e0` | `0x8003f458` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f458` | `0x8003f4d0` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f4d0` | `0x8003f548` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f548` | `0x8003f5c0` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f5c0` | `0x8003f638` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f638` | `0x8003f6b0` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f6b0` | `0x8003f728` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f728` | `0x8003f7a0` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f7a0` | `0x8003f818` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f818` | `0x8003f890` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f890` | `0x8003f908` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f908` | `0x8003f980` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f980` | `0x8003f9f0` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f9f0` | `0x8003fa60` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fa60` | `0x8003fad0` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fad0` | `0x8003fb40` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fb40` | `0x8003fbb0` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fbb0` | `0x8003fc20` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fc20` | `0x8003fc90` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fc90` | `0x8003fd00` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fd00` | `0x8003fd70` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fd70` | `0x8003fde0` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fde0` | `0x8003fe50` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fe50` | `0x8003fec0` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fec0` | `0x8003ff30` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003ff30` | `0x8003ffa0` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003ffa0` | `0x80040010` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040010` | `0x80040080` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040080` | `0x80040098` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040098` | `0x800400ac` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800400ac` | `0x80040138` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040138` | `0x80040150` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040150` | `0x80040164` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040164` | `0x800401ec` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800401ec` | `0x80040204` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040204` | `0x80040218` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040218` | `0x80040238` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040238` | `0x80040240` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040240` | `0x8004024c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8004024c` | `0x80040250` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040250` | `0x800402d4` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800402d4` | `0x8004037c` | 168 | `h_ADD` | UNCONVERTED |
| `0x8004037c` | `0x800404b0` | 308 | `h_MUL` | UNCONVERTED |
| `0x800404b0` | `0x80040558` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040558` | `0x80040650` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040650` | `0x800406e8` | 152 | `h_LT` | UNCONVERTED |
| `0x800406e8` | `0x80040780` | 152 | `h_GT` | UNCONVERTED |
| `0x80040780` | `0x80040814` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040814` | `0x800408a8` | 148 | `h_SGT` | UNCONVERTED |
| `0x800408a8` | `0x8004092c` | 132 | `h_EQ` | UNCONVERTED |
| `0x8004092c` | `0x8004098c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004098c` | `0x80040a00` | 116 | `h_AND` | UNCONVERTED |
| `0x80040a00` | `0x80040a74` | 116 | `h_OR` | UNCONVERTED |
| `0x80040a74` | `0x80040ae8` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040ae8` | `0x80040b48` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040b48` | `0x80040c34` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040c34` | `0x80040dd4` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040dd4` | `0x80040f74` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040f74` | `0x80041128` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041128` | `0x80041228` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041228` | `0x8004125c` | 52 | `h_POP` | UNCONVERTED |
| `0x8004125c` | `0x800415a8` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800415a8` | `0x80041888` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041888` | `0x800419a8` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800419a8` | `0x800419ec` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800419ec` | `0x80041a30` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041a30` | `0x80041a80` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041a80` | `0x80041ad0` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041ad0` | `0x80041b20` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041b20` | `0x80041b70` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041b70` | `0x80041bc0` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041bc0` | `0x80041c10` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041c10` | `0x80041c60` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041c60` | `0x80041cb0` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041cb0` | `0x80041d00` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041d00` | `0x80041d50` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041d50` | `0x80041da0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041da0` | `0x80041df0` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041df0` | `0x80041e40` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041e40` | `0x80041e90` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041e90` | `0x80041ee0` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041ee0` | `0x80041f78` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041f78` | `0x80042064` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042064` | `0x800420a8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800420a8` | `0x800422c4` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x800422c4` | `0x80042494` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042494` | `0x800424d8` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800424d8` | `0x800426a4` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800426a4` | `0x800426ac` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800426ac` | `0x8004276c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004276c` | `0x80042860` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042860` | `0x800428a4` | 68 | `h_PC` | UNCONVERTED |
| `0x800428a4` | `0x80042b2c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042b2c` | `0x80042e20` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042e20` | `0x80043134` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043134` | `0x80043468` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043468` | `0x800437bc` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800437bc` | `0x80043b30` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043b30` | `0x80043dd8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043dd8` | `0x800440e0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800440e0` | `0x8004474c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004474c` | `0x80044cf4` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044cf4` | `0x80045274` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045274` | `0x80045b00` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045b00` | `0x80045bec` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045bec` | `0x80045cbc` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045cbc` | `0x80045f3c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80045f3c` | `0x800468d4` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800468d4` | `0x80046eb8` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80046eb8` | `0x80046ed4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046ed4` | `0x800483f8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800483f8` | `0x80048444` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048444` | `0x800485e8` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800485e8` | `0x800493b0` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800493b0` | `0x8004b65c` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b65c` | `0x8004c7d4` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c7d4` | `0x8004d438` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d438` | `0x8004e240` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e240` | `0x8004eea4` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004eea4` | `0x8004f75c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f75c` | `0x80050050` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050050` | `0x800505ec` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800505ec` | `0x80050c98` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050c98` | `0x80050cb8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050cb8` | `0x80051364` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051364` | `0x80051384` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051384` | `0x80051cb4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051cb4` | `0x80052000` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052000` | `0x80052170` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052170` | `0x80052174` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052174` | `0x800521fc` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800521fc` | `0x800523f0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800523f0` | `0x80052420` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052420` | `0x80052434` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052434` | `0x80052444` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052444` | `0x80052474` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052474` | `0x80052668` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052668` | `0x80052698` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052698` | `0x800526ac` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800526ac` | `0x800526bc` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800526bc` | `0x800526ec` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800526ec` | `0x80052710` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052710` | `0x80052740` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052740` | `0x80052934` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052934` | `0x80052964` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052964` | `0x80052978` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052978` | `0x80052988` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052988` | `0x800529b8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800529b8` | `0x80052bac` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052bac` | `0x80052bdc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052bdc` | `0x80052bf0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bf0` | `0x80052c00` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052c00` | `0x80052c30` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052c30` | `0x80052e24` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052e24` | `0x80052e54` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052e54` | `0x80052e68` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e68` | `0x80052e78` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052e78` | `0x80052ea8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052ea8` | `0x80052ea8` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052ea8` | `0x80052ec4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053050` | `0x80053284` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053784` | `0x800538b4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800538b4` | `0x80053910` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053910` | `0x80053930` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053930` | `0x80053a6c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053c3c` | `0x80053c48` | 12 | `requests_hash_verify` | TAIL |
