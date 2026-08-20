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

`.text` = [0x80000000, 0x800543cc), 345036 bytes (`RegionMap.textSizeBytes = 0x543cc`)

- symbols in `.text`: 910 (443 converted, 467 unconverted)
- covered by converted `_prog`s: 120572 bytes (34.94%)
- NOT covered: 224464 bytes (65.06%), 468 ranges

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
| `0x80004fd4` | `0x8000517c` | 424 | `rlp_recursive_decode` | UNCONVERTED |
| `0x8000517c` | `0x800052f0` | 372 | `rlp_recursive_decode_items` | UNCONVERTED |
| `0x800052f0` | `0x80005314` | 36 | `rlp_recursive_decode_read_be` | UNCONVERTED |
| `0x80005314` | `0x8000535c` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x8000535c` | `0x800053c4` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800053c4` | `0x8000541c` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x8000541c` | `0x80005484` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005484` | `0x80005678` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009954` | `0x80009b18` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009b18` | `0x80009b84` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a440` | `0x8000a640` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a640` | `0x8000a780` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a780` | `0x8000aa3c` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000aa3c` | `0x8000ab2c` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ab2c` | `0x8000ac9c` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e598` | `0x8000f8b4` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fce4` | `0x8000fec4` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fec4` | `0x8000ffa8` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000ffa8` | `0x80010084` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x80010084` | `0x80010118` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010118` | `0x800101d4` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x800101d4` | `0x80010284` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x80010284` | `0x80010368` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010368` | `0x800103a4` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103a4` | `0x800104d4` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x800104d4` | `0x800105f8` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800105f8` | `0x800106a8` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106a8` | `0x80010824` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010824` | `0x800108fc` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800108fc` | `0x80010a8c` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010a8c` | `0x80010c28` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c28` | `0x80010cd8` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010cd8` | `0x80010d40` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d40` | `0x80010ddc` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010ddc` | `0x80011410` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011410` | `0x800116f8` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800116f8` | `0x80011a50` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011a50` | `0x80011f2c` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f2c` | `0x800121d0` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800121d0` | `0x800122ec` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800122ec` | `0x800125a4` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125a4` | `0x800127c4` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800127c4` | `0x80012b5c` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012b5c` | `0x80012c70` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012c70` | `0x80012c90` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012c90` | `0x80012f18` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f18` | `0x80012ffc` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012ffc` | `0x800130a4` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130a4` | `0x800137d8` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800137d8` | `0x80013e10` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001414c` | `0x80014160` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80014160` | `0x8001416c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x8001416c` | `0x800141bc` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800141bc` | `0x800141dc` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800141dc` | `0x80014240` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014240` | `0x800144e8` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800144e8` | `0x8001473c` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x8001473c` | `0x800148f0` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800154f0` | `0x800156e8` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a08` | `0x80015c38` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016028` | `0x80018b24` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80018b24` | `0x800198b8` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800198b8` | `0x80019ad4` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019dbc` | `0x80019e50` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a648` | `0x8001a8a0` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a8a0` | `0x8001ab18` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001ab18` | `0x8001adac` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b3a8` | `0x8001b6c4` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ba8c` | `0x8001bd04` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd04` | `0x8001bfa8` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bfa8` | `0x8001ca6c` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cd80` | `0x8001cdc8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d458` | `0x8001d640` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d640` | `0x8001d69c` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d69c` | `0x8001d768` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d768` | `0x8001d83c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d83c` | `0x8001e7cc` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f0a0` | `0x8001f1b4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f1b4` | `0x8001f5e8` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x8002029c` | `0x800202dc` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8002053c` | `0x80020684` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020684` | `0x800206b4` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c04` | `0x80020d94` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021f88` | `0x800220a4` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800220a4` | `0x80022268` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80022268` | `0x800224f8` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022bcc` | `0x80022cec` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023a08` | `0x80023a24` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a24` | `0x80023a98` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023a98` | `0x80023ae8` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023ae8` | `0x80023b14` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b14` | `0x80023bf4` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023bf4` | `0x80023c74` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023c74` | `0x80023ca4` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023de4` | `0x80023ea8` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023ea8` | `0x80023efc` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023efc` | `0x80023f2c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023f2c` | `0x80023f6c` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023f6c` | `0x80023fa4` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023fa4` | `0x80023fe4` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80024144` | `0x8002415c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x8002511c` | `0x80025318` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800253b0` | `0x800254bc` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025520` | `0x800256e8` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800256e8` | `0x800259d0` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800259d0` | `0x80025ab8` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025ab8` | `0x80025b94` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025b94` | `0x80025c6c` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80026020` | `0x80026144` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80026144` | `0x8002623c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026a64` | `0x80026a74` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026c58` | `0x80026e70` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026e70` | `0x80027064` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800273f8` | `0x80027a7c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028998` | `0x80028eb4` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028f14` | `0x80028fb4` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029c00` | `0x8002a3f4` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002aa88` | `0x8002ad24` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad24` | `0x8002ad5c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c9b8` | `0x8002ceb0` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002ceb0` | `0x8002dad4` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002dad4` | `0x8002e0a4` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e0a4` | `0x8002fa64` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fa64` | `0x8002fa88` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fa88` | `0x8002faa4` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002faa4` | `0x8002fd68` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fd68` | `0x8002fd78` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fd78` | `0x8002fdac` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fdac` | `0x8002fdc4` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fdc4` | `0x8002fdd4` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fdd4` | `0x8002fe08` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe08` | `0x8002fe10` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe10` | `0x8002febc` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002febc` | `0x8002fec8` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002fec8` | `0x8002fef0` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002fef0` | `0x8002ff30` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff30` | `0x8002ff60` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ff60` | `0x8002ff60` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ff60` | `0x8002ff78` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ff78` | `0x8002ff80` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ff80` | `0x8002ff8c` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002ff8c` | `0x8002ffa4` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002ffa4` | `0x8002ffbc` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002ffbc` | `0x8002ffd0` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002ffd0` | `0x8002fff0` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002fff0` | `0x80030004` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030004` | `0x80030030` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x80030030` | `0x80030078` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x80030078` | `0x80030158` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x80030158` | `0x80030208` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030208` | `0x80030228` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030228` | `0x8003029c` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8003029c` | `0x800302ac` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x800302ac` | `0x800302b8` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x800302b8` | `0x8003039c` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8003039c` | `0x800303c4` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x800303c4` | `0x800303d8` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x800303d8` | `0x800303d8` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x800303d8` | `0x800303d8` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x800303d8` | `0x800303f8` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x800303f8` | `0x80030428` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030428` | `0x8003044c` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8003044c` | `0x8003046c` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8003046c` | `0x80030470` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x80030470` | `0x80030510` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030510` | `0x80030520` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030520` | `0x80030530` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x80030530` | `0x80030660` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x80030660` | `0x80030660` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x80030660` | `0x800307fc` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800307fc` | `0x800307fc` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800307fc` | `0x8003085c` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031614` | `0x8003163c` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x8003163c` | `0x8003184c` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x8003194c` | `0x800319f8` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800319f8` | `0x80031a7c` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031a7c` | `0x80031afc` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031afc` | `0x80031bb4` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031bb4` | `0x80031c28` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c28` | `0x80031dec` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031dec` | `0x80031e5c` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031e5c` | `0x80031ed4` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031ed4` | `0x80032084` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80032084` | `0x80032100` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032100` | `0x80032150` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80032150` | `0x800321a0` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800321a0` | `0x800321d0` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x800321d0` | `0x80032214` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032214` | `0x80032258` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80032258` | `0x80032308` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032308` | `0x80032464` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80032464` | `0x80032760` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80032760` | `0x8003293c` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x8003293c` | `0x800329e8` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800329e8` | `0x80032b60` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032b60` | `0x80032d2c` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d2c` | `0x80032e60` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032f50` | `0x8003302c` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x8003302c` | `0x8003317c` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x8003317c` | `0x80033358` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033508` | `0x800336f4` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800336f4` | `0x80033748` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033748` | `0x80033790` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033790` | `0x80033864` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033864` | `0x80033944` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033944` | `0x80033afc` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034514` | `0x80034590` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034590` | `0x8003467c` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034ce0` | `0x80034d50` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034d50` | `0x80034db0` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x8003518c` | `0x800351e0` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800353a8` | `0x80035614` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035614` | `0x80035954` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035954` | `0x80035c04` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c04` | `0x80035f38` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035f38` | `0x800362c0` | 904 | `bng2_add` | UNCONVERTED |
| `0x800362c0` | `0x800363e0` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036400` | `0x80036830` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80036830` | `0x80036c74` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036cc8` | `0x80036e74` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x800372e8` | `0x800374ac` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037c3c` | `0x80037f14` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038800` | `0x80038890` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038890` | `0x80038960` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038b38` | `0x80038b94` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038d84` | `0x80038ff0` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038ff0` | `0x80039310` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039310` | `0x800395c0` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800395c0` | `0x8003979c` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x8003979c` | `0x80039ae4` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c30` | `0x8003b494` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b494` | `0x8003c6d0` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c7f4` | `0x8003c910` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c920` | `0x8003c950` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c950` | `0x8003ceec` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003ceec` | `0x8003d1fc` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d1fc` | `0x8003d204` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d204` | `0x8003d208` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d208` | `0x8003d3ec` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d4e4` | `0x8003d72c` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d72c` | `0x8003dd90` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003dd90` | `0x8003deac` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003deac` | `0x8003e0c4` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e0c4` | `0x8003e104` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e104` | `0x8003e14c` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e14c` | `0x8003e19c` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e19c` | `0x8003e1f4` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e1f4` | `0x8003e254` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e254` | `0x8003e2bc` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e2bc` | `0x8003e32c` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e32c` | `0x8003e3a4` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e3a4` | `0x8003e424` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e424` | `0x8003e4ac` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e4ac` | `0x8003e53c` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e53c` | `0x8003e5d4` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e5d4` | `0x8003e674` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e674` | `0x8003e71c` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e71c` | `0x8003e7cc` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e7cc` | `0x8003e884` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e884` | `0x8003e944` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e944` | `0x8003ea0c` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea0c` | `0x8003eadc` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eadc` | `0x8003ebb4` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ebb4` | `0x8003ec94` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ec94` | `0x8003ed7c` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ed7c` | `0x8003ee6c` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003ee6c` | `0x8003ef64` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ef64` | `0x8003f064` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f064` | `0x8003f16c` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f16c` | `0x8003f27c` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f27c` | `0x8003f394` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f394` | `0x8003f4b4` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f4b4` | `0x8003f5dc` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f5dc` | `0x8003f70c` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f70c` | `0x8003f844` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f844` | `0x8003f984` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f984` | `0x8003f9fc` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f9fc` | `0x8003fa74` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fa74` | `0x8003faec` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003faec` | `0x8003fb64` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fb64` | `0x8003fbdc` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fbdc` | `0x8003fc54` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fc54` | `0x8003fccc` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fccc` | `0x8003fd44` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fd44` | `0x8003fdbc` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fdbc` | `0x8003fe34` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe34` | `0x8003feac` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003feac` | `0x8003ff24` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff24` | `0x8003ff9c` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003ff9c` | `0x80040014` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040014` | `0x8004008c` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8004008c` | `0x80040104` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040104` | `0x80040174` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x80040174` | `0x800401e4` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x800401e4` | `0x80040254` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x80040254` | `0x800402c4` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x800402c4` | `0x80040334` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x80040334` | `0x800403a4` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800403a4` | `0x80040414` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040414` | `0x80040484` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x80040484` | `0x800404f4` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x800404f4` | `0x80040564` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x80040564` | `0x800405d4` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x800405d4` | `0x80040644` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040644` | `0x800406b4` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x800406b4` | `0x80040724` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040724` | `0x80040794` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040794` | `0x80040804` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040804` | `0x8004081c` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8004081c` | `0x80040830` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80040830` | `0x800408bc` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x800408bc` | `0x800408d4` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800408d4` | `0x800408e8` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800408e8` | `0x80040970` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040970` | `0x80040988` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040988` | `0x8004099c` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8004099c` | `0x800409bc` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x800409bc` | `0x800409c4` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x800409c4` | `0x800409d0` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x800409d0` | `0x800409d4` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800409d4` | `0x80040a58` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040a58` | `0x80040b00` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b00` | `0x80040c34` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c34` | `0x80040cdc` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040cdc` | `0x80040dd4` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040dd4` | `0x80040e6c` | 152 | `h_LT` | UNCONVERTED |
| `0x80040e6c` | `0x80040f04` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f04` | `0x80040f98` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040f98` | `0x8004102c` | 148 | `h_SGT` | UNCONVERTED |
| `0x8004102c` | `0x800410b0` | 132 | `h_EQ` | UNCONVERTED |
| `0x800410b0` | `0x80041110` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041110` | `0x80041184` | 116 | `h_AND` | UNCONVERTED |
| `0x80041184` | `0x800411f8` | 116 | `h_OR` | UNCONVERTED |
| `0x800411f8` | `0x8004126c` | 116 | `h_XOR` | UNCONVERTED |
| `0x8004126c` | `0x800412cc` | 96 | `h_NOT` | UNCONVERTED |
| `0x800412cc` | `0x800413b8` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800413b8` | `0x80041558` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041558` | `0x800416f8` | 416 | `h_SHR` | UNCONVERTED |
| `0x800416f8` | `0x800418ac` | 436 | `h_SAR` | UNCONVERTED |
| `0x800418ac` | `0x800419ac` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800419ac` | `0x800419e0` | 52 | `h_POP` | UNCONVERTED |
| `0x800419e0` | `0x80041d2c` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d2c` | `0x8004200c` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x8004200c` | `0x8004212c` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x8004212c` | `0x80042170` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80042170` | `0x800421b4` | 68 | `h_GAS` | UNCONVERTED |
| `0x800421b4` | `0x80042204` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042204` | `0x80042254` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80042254` | `0x800422a4` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800422a4` | `0x800422f4` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x800422f4` | `0x80042344` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80042344` | `0x80042394` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80042394` | `0x800423e4` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800423e4` | `0x80042434` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80042434` | `0x80042484` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80042484` | `0x800424d4` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800424d4` | `0x80042524` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80042524` | `0x80042574` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042574` | `0x800425c4` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x800425c4` | `0x80042614` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042614` | `0x80042664` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042664` | `0x800426fc` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800426fc` | `0x800427e8` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800427e8` | `0x8004282c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004282c` | `0x80042a48` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042a48` | `0x80042c18` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c18` | `0x80042c5c` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042c5c` | `0x80042e28` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e28` | `0x80042e30` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e30` | `0x80042ef0` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042ef0` | `0x80042fe4` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042fe4` | `0x80043028` | 68 | `h_PC` | UNCONVERTED |
| `0x80043028` | `0x800432b0` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800432b0` | `0x800435a4` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800435a4` | `0x800438b8` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800438b8` | `0x80043bec` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043bec` | `0x80043f40` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043f40` | `0x800442b4` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800442b4` | `0x8004455c` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x8004455c` | `0x80044864` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044864` | `0x80044ed0` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044ed0` | `0x80045478` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80045478` | `0x800459f8` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800459f8` | `0x80046284` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80046284` | `0x80046370` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80046370` | `0x80046440` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80046440` | `0x800466c0` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x800466c0` | `0x80047058` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80047058` | `0x8004763c` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x8004763c` | `0x80047658` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047658` | `0x80048b7c` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048b7c` | `0x80048bc8` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048bc8` | `0x80048d6c` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048d6c` | `0x80049b34` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b34` | `0x8004bde0` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004bde0` | `0x8004cf58` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cf58` | `0x8004dbbc` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dbbc` | `0x8004e9c4` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e9c4` | `0x8004f628` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f628` | `0x8004fee0` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fee0` | `0x800507d4` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800507d4` | `0x80050d70` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050d70` | `0x8005141c` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x8005141c` | `0x8005143c` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x8005143c` | `0x80051ae8` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051ae8` | `0x80051b08` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b08` | `0x80052438` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052438` | `0x80052784` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052784` | `0x800528f4` | 368 | `h_STOP` | UNCONVERTED |
| `0x800528f4` | `0x800528f8` | 4 | `h_invalid` | UNCONVERTED |
| `0x800528f8` | `0x80052980` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80052980` | `0x80052b74` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052b74` | `0x80052ba4` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052ba4` | `0x80052bb8` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bb8` | `0x80052bc8` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052bc8` | `0x80052bf8` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052bf8` | `0x80052dec` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052dec` | `0x80052e1c` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e1c` | `0x80052e30` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e30` | `0x80052e40` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052e40` | `0x80052e70` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052e70` | `0x80052e94` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052e94` | `0x80052ec4` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052ec4` | `0x800530b8` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800530b8` | `0x800530e8` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x800530e8` | `0x800530fc` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x800530fc` | `0x8005310c` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x8005310c` | `0x8005313c` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x8005313c` | `0x80053330` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80053330` | `0x80053360` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80053360` | `0x80053374` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053374` | `0x80053384` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80053384` | `0x800533b4` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800533b4` | `0x800535a8` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800535a8` | `0x800535d8` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800535d8` | `0x800535ec` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800535ec` | `0x800535fc` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800535fc` | `0x8005362c` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005362c` | `0x8005362c` | 0 | `.exit_label` | UNCONVERTED |
| `0x8005362c` | `0x80053648` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800537d4` | `0x80053a08` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053f08` | `0x80054038` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054038` | `0x80054094` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054094` | `0x800540b4` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800540b4` | `0x800541f0` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x800543c0` | `0x800543cc` | 12 | `requests_hash_verify` | TAIL |
