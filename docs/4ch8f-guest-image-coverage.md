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
not linked** (101 of 543 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x8005440c), 345100 bytes (`RegionMap.textSizeBytes = 0x5440c`)

- symbols in `.text`: 909 (442 converted, 467 unconverted)
- covered by converted `_prog`s: 120620 bytes (34.95%)
- NOT covered: 224480 bytes (65.05%), 468 ranges

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
| `0x80004fd0` | `0x80005178` | 424 | `rlp_recursive_decode` | UNCONVERTED |
| `0x80005178` | `0x800052ec` | 372 | `rlp_recursive_decode_items` | UNCONVERTED |
| `0x800052ec` | `0x80005310` | 36 | `rlp_recursive_decode_read_be` | UNCONVERTED |
| `0x80005310` | `0x80005358` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80005358` | `0x800053c0` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800053c0` | `0x80005418` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x80005418` | `0x80005480` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005480` | `0x80005674` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009950` | `0x80009b14` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009b14` | `0x80009b80` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a43c` | `0x8000a63c` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a63c` | `0x8000a77c` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a77c` | `0x8000aa38` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000aa38` | `0x8000ab28` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ab28` | `0x8000ac98` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e5b8` | `0x8000f8d4` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fd04` | `0x8000fee4` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fee4` | `0x8000ffc8` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000ffc8` | `0x800100a4` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x800100a4` | `0x80010138` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010138` | `0x800101f4` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x800101f4` | `0x800102a4` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x800102a4` | `0x80010388` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010388` | `0x800103c4` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103c4` | `0x800104f4` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x800104f4` | `0x80010618` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010618` | `0x800106c8` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106c8` | `0x80010844` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010844` | `0x8001091c` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8001091c` | `0x80010aac` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010aac` | `0x80010c48` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c48` | `0x80010cf8` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010cf8` | `0x80010d60` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d60` | `0x80010dfc` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010dfc` | `0x80011430` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011430` | `0x80011718` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011718` | `0x80011a70` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011a70` | `0x80011f4c` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f4c` | `0x800121f0` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800121f0` | `0x8001230c` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x8001230c` | `0x800125c4` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125c4` | `0x800127e4` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800127e4` | `0x80012b7c` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012b7c` | `0x80012c90` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012c90` | `0x80012cb0` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012cb0` | `0x80012f38` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f38` | `0x8001301c` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x8001301c` | `0x800130c4` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130c4` | `0x800137f8` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800137f8` | `0x80013e30` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001416c` | `0x80014180` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80014180` | `0x8001418c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x8001418c` | `0x800141dc` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800141dc` | `0x800141fc` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800141fc` | `0x80014260` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014260` | `0x80014508` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014508` | `0x8001475c` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x8001475c` | `0x80014910` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015510` | `0x80015708` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a28` | `0x80015c58` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016048` | `0x80018b54` | 11020 | `block_verdict` | UNCONVERTED |
| `0x80018b54` | `0x800198e8` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800198e8` | `0x80019b04` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019dec` | `0x80019e80` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a678` | `0x8001a8d0` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a8d0` | `0x8001ab48` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001ab48` | `0x8001addc` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b3d8` | `0x8001b6f4` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001babc` | `0x8001bd34` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd34` | `0x8001bfd8` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bfd8` | `0x8001ca9c` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cdb0` | `0x8001cdf8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d498` | `0x8001d680` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d680` | `0x8001d6dc` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d6dc` | `0x8001d7a8` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7a8` | `0x8001d87c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d87c` | `0x8001e80c` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f0e0` | `0x8001f1f4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f1f4` | `0x8001f628` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x800202dc` | `0x8002031c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8002057c` | `0x800206c4` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800206c4` | `0x800206f4` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c44` | `0x80020dd4` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021fc8` | `0x800220e4` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800220e4` | `0x800222a8` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x800222a8` | `0x80022538` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022c0c` | `0x80022d2c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023a48` | `0x80023a64` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a64` | `0x80023ad8` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023ad8` | `0x80023b28` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b28` | `0x80023b54` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b54` | `0x80023c34` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c34` | `0x80023cb4` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023cb4` | `0x80023ce4` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023e24` | `0x80023ee8` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023ee8` | `0x80023f3c` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f3c` | `0x80023f6c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023f6c` | `0x80023fac` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023fac` | `0x80023fe4` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023fe4` | `0x80024024` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80024184` | `0x8002419c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x8002515c` | `0x80025358` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800253f0` | `0x800254fc` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025560` | `0x80025728` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80025728` | `0x80025a10` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025a10` | `0x80025af8` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025af8` | `0x80025bd4` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025bd4` | `0x80025cac` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80026060` | `0x80026184` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80026184` | `0x8002627c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026aa4` | `0x80026ab4` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026c98` | `0x80026eb0` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026eb0` | `0x800270a4` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80027438` | `0x80027abc` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800289d8` | `0x80028ef4` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028f54` | `0x80028ff4` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029c40` | `0x8002a434` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002aac8` | `0x8002ad64` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad64` | `0x8002ad9c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c9f8` | `0x8002cef0` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cef0` | `0x8002db14` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db14` | `0x8002e0e4` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e0e4` | `0x8002faa4` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002faa4` | `0x8002fac8` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fac8` | `0x8002fae4` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fae4` | `0x8002fda8` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fda8` | `0x8002fdb8` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fdb8` | `0x8002fdec` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fdec` | `0x8002fe04` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe04` | `0x8002fe14` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe14` | `0x8002fe48` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe48` | `0x8002fe50` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe50` | `0x8002fefc` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002fefc` | `0x8002ff08` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff08` | `0x8002ff30` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff30` | `0x8002ff70` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff70` | `0x8002ffa0` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffa0` | `0x8002ffa0` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffa0` | `0x8002ffb8` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ffb8` | `0x8002ffc0` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ffc0` | `0x8002ffcc` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002ffcc` | `0x8002ffe4` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002ffe4` | `0x8002fffc` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fffc` | `0x80030010` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030010` | `0x80030030` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030030` | `0x80030044` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030044` | `0x80030070` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x80030070` | `0x800300b8` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300b8` | `0x80030198` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x80030198` | `0x80030248` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030248` | `0x80030268` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030268` | `0x800302dc` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x800302dc` | `0x800302ec` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x800302ec` | `0x800302f8` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x800302f8` | `0x800303dc` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x800303dc` | `0x80030404` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x80030404` | `0x80030418` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030418` | `0x80030418` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030418` | `0x80030418` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030418` | `0x80030438` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030438` | `0x80030468` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030468` | `0x8003048c` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8003048c` | `0x800304ac` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304ac` | `0x800304b0` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304b0` | `0x80030550` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030550` | `0x80030560` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030560` | `0x80030570` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x80030570` | `0x800306a0` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306a0` | `0x800306a0` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306a0` | `0x8003083c` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8003083c` | `0x8003083c` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8003083c` | `0x8003089c` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031654` | `0x8003167c` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x8003167c` | `0x8003188c` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x8003198c` | `0x80031a38` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a38` | `0x80031abc` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031abc` | `0x80031b3c` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031b3c` | `0x80031bf4` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031bf4` | `0x80031c68` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c68` | `0x80031e2c` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e2c` | `0x80031e9c` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031e9c` | `0x80031f14` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f14` | `0x800320c4` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320c4` | `0x80032140` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032140` | `0x80032190` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80032190` | `0x800321e0` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800321e0` | `0x80032210` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032210` | `0x80032254` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032254` | `0x80032298` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80032298` | `0x80032348` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032348` | `0x800324a4` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324a4` | `0x800327a0` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327a0` | `0x8003297c` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8003297c` | `0x80032a28` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a28` | `0x80032ba0` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032ba0` | `0x80032d6c` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d6c` | `0x80032ea0` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032f90` | `0x8003306c` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8003306c` | `0x800331bc` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331bc` | `0x80033398` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033548` | `0x80033734` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80033734` | `0x80033788` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033788` | `0x800337d0` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800337d0` | `0x800338a4` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338a4` | `0x80033984` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033984` | `0x80033b3c` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034554` | `0x800345d0` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800345d0` | `0x800346bc` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d20` | `0x80034d90` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034d90` | `0x80034df0` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800351cc` | `0x80035220` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800353e8` | `0x80035654` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035654` | `0x80035994` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035994` | `0x80035c44` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c44` | `0x80035f78` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035f78` | `0x80036300` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036300` | `0x80036420` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036440` | `0x80036870` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80036870` | `0x80036cb4` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d08` | `0x80036eb4` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037328` | `0x800374ec` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037c7c` | `0x80037f54` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038840` | `0x800388d0` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800388d0` | `0x800389a0` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038b78` | `0x80038bd4` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038dc4` | `0x80039030` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039030` | `0x80039350` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039350` | `0x80039600` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039600` | `0x800397dc` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800397dc` | `0x80039b24` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c70` | `0x8003b4d4` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b4d4` | `0x8003c710` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c834` | `0x8003c950` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c960` | `0x8003c990` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c990` | `0x8003cf2c` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf2c` | `0x8003d23c` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d23c` | `0x8003d244` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d244` | `0x8003d248` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d248` | `0x8003d42c` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d524` | `0x8003d76c` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d76c` | `0x8003ddd0` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ddd0` | `0x8003deec` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003deec` | `0x8003e104` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e104` | `0x8003e144` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e144` | `0x8003e18c` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e18c` | `0x8003e1dc` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e1dc` | `0x8003e234` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e234` | `0x8003e294` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e294` | `0x8003e2fc` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e2fc` | `0x8003e36c` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e36c` | `0x8003e3e4` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e3e4` | `0x8003e464` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e464` | `0x8003e4ec` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e4ec` | `0x8003e57c` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e57c` | `0x8003e614` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e614` | `0x8003e6b4` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6b4` | `0x8003e75c` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e75c` | `0x8003e80c` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e80c` | `0x8003e8c4` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8c4` | `0x8003e984` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e984` | `0x8003ea4c` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea4c` | `0x8003eb1c` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb1c` | `0x8003ebf4` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ebf4` | `0x8003ecd4` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ecd4` | `0x8003edbc` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003edbc` | `0x8003eeac` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eeac` | `0x8003efa4` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efa4` | `0x8003f0a4` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0a4` | `0x8003f1ac` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1ac` | `0x8003f2bc` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2bc` | `0x8003f3d4` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f3d4` | `0x8003f4f4` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f4f4` | `0x8003f61c` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f61c` | `0x8003f74c` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f74c` | `0x8003f884` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f884` | `0x8003f9c4` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9c4` | `0x8003fa3c` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa3c` | `0x8003fab4` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fab4` | `0x8003fb2c` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb2c` | `0x8003fba4` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fba4` | `0x8003fc1c` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc1c` | `0x8003fc94` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fc94` | `0x8003fd0c` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd0c` | `0x8003fd84` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fd84` | `0x8003fdfc` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fdfc` | `0x8003fe74` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe74` | `0x8003feec` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003feec` | `0x8003ff64` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff64` | `0x8003ffdc` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003ffdc` | `0x80040054` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040054` | `0x800400cc` | 120 | `h_DUP15` | UNCONVERTED |
| `0x800400cc` | `0x80040144` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040144` | `0x800401b4` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401b4` | `0x80040224` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x80040224` | `0x80040294` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x80040294` | `0x80040304` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x80040304` | `0x80040374` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x80040374` | `0x800403e4` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800403e4` | `0x80040454` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040454` | `0x800404c4` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404c4` | `0x80040534` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x80040534` | `0x800405a4` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405a4` | `0x80040614` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x80040614` | `0x80040684` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040684` | `0x800406f4` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x800406f4` | `0x80040764` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040764` | `0x800407d4` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800407d4` | `0x80040844` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040844` | `0x8004085c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8004085c` | `0x80040870` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80040870` | `0x800408fc` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x800408fc` | `0x80040914` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040914` | `0x80040928` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040928` | `0x800409b0` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409b0` | `0x800409c8` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800409c8` | `0x800409dc` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800409dc` | `0x800409fc` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x800409fc` | `0x80040a04` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a04` | `0x80040a10` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a10` | `0x80040a14` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a14` | `0x80040a98` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040a98` | `0x80040b40` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b40` | `0x80040c74` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c74` | `0x80040d1c` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d1c` | `0x80040e14` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e14` | `0x80040eac` | 152 | `h_LT` | UNCONVERTED |
| `0x80040eac` | `0x80040f44` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f44` | `0x80040fd8` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040fd8` | `0x8004106c` | 148 | `h_SGT` | UNCONVERTED |
| `0x8004106c` | `0x800410f0` | 132 | `h_EQ` | UNCONVERTED |
| `0x800410f0` | `0x80041150` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041150` | `0x800411c4` | 116 | `h_AND` | UNCONVERTED |
| `0x800411c4` | `0x80041238` | 116 | `h_OR` | UNCONVERTED |
| `0x80041238` | `0x800412ac` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412ac` | `0x8004130c` | 96 | `h_NOT` | UNCONVERTED |
| `0x8004130c` | `0x800413f8` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800413f8` | `0x80041598` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041598` | `0x80041738` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041738` | `0x800418ec` | 436 | `h_SAR` | UNCONVERTED |
| `0x800418ec` | `0x800419ec` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800419ec` | `0x80041a20` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a20` | `0x80041d6c` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d6c` | `0x8004204c` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x8004204c` | `0x8004216c` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x8004216c` | `0x800421b0` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421b0` | `0x800421f4` | 68 | `h_GAS` | UNCONVERTED |
| `0x800421f4` | `0x80042244` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042244` | `0x80042294` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80042294` | `0x800422e4` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800422e4` | `0x80042334` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80042334` | `0x80042384` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80042384` | `0x800423d4` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800423d4` | `0x80042424` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80042424` | `0x80042474` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80042474` | `0x800424c4` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424c4` | `0x80042514` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80042514` | `0x80042564` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80042564` | `0x800425b4` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425b4` | `0x80042604` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042604` | `0x80042654` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042654` | `0x800426a4` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426a4` | `0x8004273c` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x8004273c` | `0x80042828` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042828` | `0x8004286c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004286c` | `0x80042a88` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042a88` | `0x80042c58` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c58` | `0x80042c9c` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042c9c` | `0x80042e68` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e68` | `0x80042e70` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e70` | `0x80042f30` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f30` | `0x80043024` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80043024` | `0x80043068` | 68 | `h_PC` | UNCONVERTED |
| `0x80043068` | `0x800432f0` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800432f0` | `0x800435e4` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800435e4` | `0x800438f8` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800438f8` | `0x80043c2c` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c2c` | `0x80043f80` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043f80` | `0x800442f4` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800442f4` | `0x8004459c` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x8004459c` | `0x800448a4` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448a4` | `0x80044f10` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f10` | `0x800454b8` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454b8` | `0x80045a38` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a38` | `0x800462c4` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462c4` | `0x800463b0` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463b0` | `0x80046480` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80046480` | `0x80046700` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046700` | `0x80047098` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80047098` | `0x8004767c` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x8004767c` | `0x80047698` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047698` | `0x80048bbc` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048bbc` | `0x80048c08` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c08` | `0x80048dac` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048dac` | `0x80049b74` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b74` | `0x8004be20` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be20` | `0x8004cf98` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cf98` | `0x8004dbfc` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dbfc` | `0x8004ea04` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea04` | `0x8004f668` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f668` | `0x8004ff20` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff20` | `0x80050814` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050814` | `0x80050db0` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050db0` | `0x8005145c` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x8005145c` | `0x8005147c` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x8005147c` | `0x80051b28` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b28` | `0x80051b48` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b48` | `0x80052478` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052478` | `0x800527c4` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527c4` | `0x80052934` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052934` | `0x80052938` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052938` | `0x800529c0` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529c0` | `0x80052bb4` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052bb4` | `0x80052be4` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052be4` | `0x80052bf8` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bf8` | `0x80052c08` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c08` | `0x80052c38` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c38` | `0x80052e2c` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e2c` | `0x80052e5c` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e5c` | `0x80052e70` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e70` | `0x80052e80` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052e80` | `0x80052eb0` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052eb0` | `0x80052ed4` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052ed4` | `0x80052f04` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f04` | `0x800530f8` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800530f8` | `0x80053128` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053128` | `0x8005313c` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x8005313c` | `0x8005314c` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x8005314c` | `0x8005317c` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x8005317c` | `0x80053370` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80053370` | `0x800533a0` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533a0` | `0x800533b4` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533b4` | `0x800533c4` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533c4` | `0x800533f4` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800533f4` | `0x800535e8` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800535e8` | `0x80053618` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053618` | `0x8005362c` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x8005362c` | `0x8005363c` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x8005363c` | `0x8005366c` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005366c` | `0x8005366c` | 0 | `.exit_label` | UNCONVERTED |
| `0x8005366c` | `0x80053688` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053814` | `0x80053a48` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053f48` | `0x80054078` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054078` | `0x800540d4` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800540d4` | `0x800540f4` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800540f4` | `0x80054230` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054400` | `0x8005440c` | 12 | `requests_hash_verify` | TAIL |
