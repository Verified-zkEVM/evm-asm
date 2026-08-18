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

`.text` = [0x80000000, 0x80053c2c), 343084 bytes (`RegionMap.textSizeBytes = 0x53c2c`)

- symbols in `.text`: 907 (443 converted, 464 unconverted)
- covered by converted `_prog`s: 119788 bytes (34.92%)
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
| `0x8002327c` | `0x80023298` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023298` | `0x8002330c` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x8002330c` | `0x8002335c` | 80 | `keccak_final` | UNCONVERTED |
| `0x8002335c` | `0x80023388` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023388` | `0x80023468` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023468` | `0x800234e8` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x800234e8` | `0x80023518` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023658` | `0x8002371c` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x8002371c` | `0x80023770` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023770` | `0x800237a0` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800237a0` | `0x800237e0` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800237e0` | `0x80023818` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023818` | `0x80023858` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800239b8` | `0x800239d0` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024990` | `0x80024b8c` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024c24` | `0x80024d30` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024d94` | `0x80024f5c` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024f5c` | `0x80025244` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025244` | `0x8002532c` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x8002532c` | `0x80025408` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025408` | `0x800254e0` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025894` | `0x800259b8` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800259b8` | `0x80025ab0` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800262d8` | `0x800262e8` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x800264cc` | `0x800266e4` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x800266e4` | `0x800268d8` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026c6c` | `0x800272f0` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x8002820c` | `0x80028728` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028788` | `0x80028828` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029474` | `0x80029c68` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a2fc` | `0x8002a598` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a598` | `0x8002a5d0` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c22c` | `0x8002c724` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c724` | `0x8002d348` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d348` | `0x8002d918` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d918` | `0x8002f2d8` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f2d8` | `0x8002f2fc` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f2fc` | `0x8002f318` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f318` | `0x8002f5dc` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f5dc` | `0x8002f5ec` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f5ec` | `0x8002f620` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f620` | `0x8002f638` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f638` | `0x8002f648` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f648` | `0x8002f67c` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f67c` | `0x8002f684` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f684` | `0x8002f730` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f730` | `0x8002f73c` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f73c` | `0x8002f764` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f764` | `0x8002f7a4` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f7a4` | `0x8002f7d4` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f7d4` | `0x8002f7d4` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f7d4` | `0x8002f7ec` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f7ec` | `0x8002f7f4` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f7f4` | `0x8002f800` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f800` | `0x8002f818` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f818` | `0x8002f830` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f830` | `0x8002f844` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f844` | `0x8002f864` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f864` | `0x8002f878` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f878` | `0x8002f8a4` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f8a4` | `0x8002f8ec` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f8ec` | `0x8002f9cc` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f9cc` | `0x8002fa7c` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fa7c` | `0x8002fa9c` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fa9c` | `0x8002fb10` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fb10` | `0x8002fb20` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fb20` | `0x8002fb2c` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fb2c` | `0x8002fc10` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fc10` | `0x8002fc38` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fc38` | `0x8002fc4c` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fc4c` | `0x8002fc4c` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fc4c` | `0x8002fc4c` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fc4c` | `0x8002fc6c` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fc6c` | `0x8002fc9c` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fc9c` | `0x8002fcc0` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fcc0` | `0x8002fce0` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fce0` | `0x8002fce4` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fce4` | `0x8002fd70` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fd70` | `0x8002fd80` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fd80` | `0x8002fd90` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fd90` | `0x8002fec0` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fec0` | `0x8002fec0` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fec0` | `0x8003005c` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8003005c` | `0x8003005c` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8003005c` | `0x800300bc` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030e74` | `0x80030e9c` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030e9c` | `0x800310ac` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800311ac` | `0x80031258` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031258` | `0x800312dc` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800312dc` | `0x8003135c` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x8003135c` | `0x80031414` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031414` | `0x80031488` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031488` | `0x8003164c` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x8003164c` | `0x800316bc` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800316bc` | `0x80031734` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031734` | `0x800318e4` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800318e4` | `0x80031960` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031960` | `0x800319b0` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800319b0` | `0x80031a00` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031a00` | `0x80031a30` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031a30` | `0x80031a74` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031a74` | `0x80031ab8` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031ab8` | `0x80031b68` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031b68` | `0x80031cc4` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031cc4` | `0x80031fc0` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031fc0` | `0x8003219c` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8003219c` | `0x80032248` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032248` | `0x800323c0` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800323c0` | `0x8003258c` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x8003258c` | `0x800326c0` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800327b0` | `0x8003288c` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8003288c` | `0x800329dc` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800329dc` | `0x80032bb8` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032d68` | `0x80032f54` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032f54` | `0x80032fa8` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032fa8` | `0x80032ff0` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032ff0` | `0x800330c4` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800330c4` | `0x800331a4` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800331a4` | `0x8003335c` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033d74` | `0x80033df0` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033df0` | `0x80033edc` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034540` | `0x800345b0` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800345b0` | `0x80034610` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800349ec` | `0x80034a40` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034c08` | `0x80034e74` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034e74` | `0x800351b4` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800351b4` | `0x80035464` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035464` | `0x80035798` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035798` | `0x80035b20` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035b20` | `0x80035c40` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035c60` | `0x80036090` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80036090` | `0x800364d4` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036528` | `0x800366d4` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036b48` | `0x80036d0c` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x8003749c` | `0x80037774` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038060` | `0x800380f0` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800380f0` | `0x800381c0` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038398` | `0x800383f4` | 92 | `blq_sub` | UNCONVERTED |
| `0x800385e4` | `0x80038850` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038850` | `0x80038b70` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038b70` | `0x80038e20` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038e20` | `0x80038ffc` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038ffc` | `0x80039344` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039490` | `0x8003acf4` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003acf4` | `0x8003bf30` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c054` | `0x8003c170` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c180` | `0x8003c1b0` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c1b0` | `0x8003c74c` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c74c` | `0x8003ca5c` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003ca5c` | `0x8003ca64` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003ca64` | `0x8003ca68` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ca68` | `0x8003cc4c` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cd44` | `0x8003cf8c` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cf8c` | `0x8003d5f0` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d5f0` | `0x8003d70c` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d70c` | `0x8003d924` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d924` | `0x8003d964` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d964` | `0x8003d9ac` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d9ac` | `0x8003d9fc` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d9fc` | `0x8003da54` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003da54` | `0x8003dab4` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dab4` | `0x8003db1c` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003db1c` | `0x8003db8c` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003db8c` | `0x8003dc04` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dc04` | `0x8003dc84` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dc84` | `0x8003dd0c` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dd0c` | `0x8003dd9c` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dd9c` | `0x8003de34` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003de34` | `0x8003ded4` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003ded4` | `0x8003df7c` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003df7c` | `0x8003e02c` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e02c` | `0x8003e0e4` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e0e4` | `0x8003e1a4` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e1a4` | `0x8003e26c` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e26c` | `0x8003e33c` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e33c` | `0x8003e414` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e414` | `0x8003e4f4` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e4f4` | `0x8003e5dc` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e5dc` | `0x8003e6cc` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e6cc` | `0x8003e7c4` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e7c4` | `0x8003e8c4` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e8c4` | `0x8003e9cc` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e9cc` | `0x8003eadc` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003eadc` | `0x8003ebf4` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ebf4` | `0x8003ed14` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ed14` | `0x8003ee3c` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ee3c` | `0x8003ef6c` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003ef6c` | `0x8003f0a4` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f0a4` | `0x8003f1e4` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f1e4` | `0x8003f25c` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f25c` | `0x8003f2d4` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f2d4` | `0x8003f34c` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f34c` | `0x8003f3c4` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f3c4` | `0x8003f43c` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f43c` | `0x8003f4b4` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f4b4` | `0x8003f52c` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f52c` | `0x8003f5a4` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f5a4` | `0x8003f61c` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f61c` | `0x8003f694` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f694` | `0x8003f70c` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f70c` | `0x8003f784` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f784` | `0x8003f7fc` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f7fc` | `0x8003f874` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f874` | `0x8003f8ec` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f8ec` | `0x8003f964` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f964` | `0x8003f9d4` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f9d4` | `0x8003fa44` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fa44` | `0x8003fab4` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fab4` | `0x8003fb24` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fb24` | `0x8003fb94` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fb94` | `0x8003fc04` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fc04` | `0x8003fc74` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fc74` | `0x8003fce4` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fce4` | `0x8003fd54` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fd54` | `0x8003fdc4` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fdc4` | `0x8003fe34` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fe34` | `0x8003fea4` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fea4` | `0x8003ff14` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003ff14` | `0x8003ff84` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003ff84` | `0x8003fff4` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fff4` | `0x80040064` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040064` | `0x8004007c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8004007c` | `0x80040090` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80040090` | `0x8004011c` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8004011c` | `0x80040134` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040134` | `0x80040148` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040148` | `0x800401d0` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800401d0` | `0x800401e8` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800401e8` | `0x800401fc` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800401fc` | `0x8004021c` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8004021c` | `0x80040224` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040224` | `0x80040230` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040230` | `0x80040234` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040234` | `0x800402b8` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800402b8` | `0x80040360` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040360` | `0x80040494` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040494` | `0x8004053c` | 168 | `h_SUB` | UNCONVERTED |
| `0x8004053c` | `0x80040634` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040634` | `0x800406cc` | 152 | `h_LT` | UNCONVERTED |
| `0x800406cc` | `0x80040764` | 152 | `h_GT` | UNCONVERTED |
| `0x80040764` | `0x800407f8` | 148 | `h_SLT` | UNCONVERTED |
| `0x800407f8` | `0x8004088c` | 148 | `h_SGT` | UNCONVERTED |
| `0x8004088c` | `0x80040910` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040910` | `0x80040970` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040970` | `0x800409e4` | 116 | `h_AND` | UNCONVERTED |
| `0x800409e4` | `0x80040a58` | 116 | `h_OR` | UNCONVERTED |
| `0x80040a58` | `0x80040acc` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040acc` | `0x80040b2c` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040b2c` | `0x80040c18` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040c18` | `0x80040db8` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040db8` | `0x80040f58` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040f58` | `0x8004110c` | 436 | `h_SAR` | UNCONVERTED |
| `0x8004110c` | `0x8004120c` | 256 | `h_CLZ` | UNCONVERTED |
| `0x8004120c` | `0x80041240` | 52 | `h_POP` | UNCONVERTED |
| `0x80041240` | `0x8004158c` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x8004158c` | `0x8004186c` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x8004186c` | `0x8004198c` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x8004198c` | `0x800419d0` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800419d0` | `0x80041a14` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041a14` | `0x80041a64` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041a64` | `0x80041ab4` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041ab4` | `0x80041b04` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041b04` | `0x80041b54` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041b54` | `0x80041ba4` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041ba4` | `0x80041bf4` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041bf4` | `0x80041c44` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041c44` | `0x80041c94` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041c94` | `0x80041ce4` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041ce4` | `0x80041d34` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041d34` | `0x80041d84` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041d84` | `0x80041dd4` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041dd4` | `0x80041e24` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041e24` | `0x80041e74` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041e74` | `0x80041ec4` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041ec4` | `0x80041f5c` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041f5c` | `0x80042048` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042048` | `0x8004208c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004208c` | `0x800422a8` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x800422a8` | `0x80042478` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042478` | `0x800424bc` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800424bc` | `0x80042688` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042688` | `0x80042690` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042690` | `0x80042750` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042750` | `0x80042844` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042844` | `0x80042888` | 68 | `h_PC` | UNCONVERTED |
| `0x80042888` | `0x80042b10` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042b10` | `0x80042e04` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042e04` | `0x80043118` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043118` | `0x8004344c` | 820 | `h_LOG2` | UNCONVERTED |
| `0x8004344c` | `0x800437a0` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800437a0` | `0x80043b14` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043b14` | `0x80043dbc` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043dbc` | `0x800440c4` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800440c4` | `0x80044730` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044730` | `0x80044cd8` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044cd8` | `0x80045258` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045258` | `0x80045ae4` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045ae4` | `0x80045bd0` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045bd0` | `0x80045ca0` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045ca0` | `0x80045f20` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80045f20` | `0x800468b8` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800468b8` | `0x80046e9c` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80046e9c` | `0x80046eb8` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046eb8` | `0x800483dc` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800483dc` | `0x80048428` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048428` | `0x800485cc` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800485cc` | `0x80049394` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049394` | `0x8004b640` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b640` | `0x8004c7b8` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c7b8` | `0x8004d41c` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d41c` | `0x8004e224` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e224` | `0x8004ee88` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ee88` | `0x8004f740` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f740` | `0x80050034` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050034` | `0x800505d0` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800505d0` | `0x80050c7c` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050c7c` | `0x80050c9c` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050c9c` | `0x80051348` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051348` | `0x80051368` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051368` | `0x80051c98` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051c98` | `0x80051fe4` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051fe4` | `0x80052154` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052154` | `0x80052158` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052158` | `0x800521e0` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800521e0` | `0x800523d4` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800523d4` | `0x80052404` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052404` | `0x80052418` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052418` | `0x80052428` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052428` | `0x80052458` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052458` | `0x8005264c` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x8005264c` | `0x8005267c` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x8005267c` | `0x80052690` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052690` | `0x800526a0` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800526a0` | `0x800526d0` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800526d0` | `0x800526f4` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x800526f4` | `0x80052724` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052724` | `0x80052918` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052918` | `0x80052948` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052948` | `0x8005295c` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x8005295c` | `0x8005296c` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x8005296c` | `0x8005299c` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x8005299c` | `0x80052b90` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052b90` | `0x80052bc0` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052bc0` | `0x80052bd4` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bd4` | `0x80052be4` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052be4` | `0x80052c14` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052c14` | `0x80052e08` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052e08` | `0x80052e38` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052e38` | `0x80052e4c` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e4c` | `0x80052e5c` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052e5c` | `0x80052e8c` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e8c` | `0x80052e8c` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052e8c` | `0x80052ea8` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053034` | `0x80053268` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053768` | `0x80053898` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053898` | `0x800538f4` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800538f4` | `0x80053914` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053914` | `0x80053a50` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053c20` | `0x80053c2c` | 12 | `requests_hash_verify` | TAIL |
