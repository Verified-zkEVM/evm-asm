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
not linked** (101 of 546 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80054094), 344212 bytes (`RegionMap.textSizeBytes = 0x54094`)

- symbols in `.text`: 907 (445 converted, 462 unconverted)
- covered by converted `_prog`s: 120772 bytes (35.09%)
- NOT covered: 223440 bytes (64.91%), 463 ranges

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
| `0x8000514c` | `0x80005340` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x8000961c` | `0x800097e0` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x800097e0` | `0x8000984c` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a108` | `0x8000a308` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a308` | `0x8000a448` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a448` | `0x8000a704` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a704` | `0x8000a7f4` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a7f4` | `0x8000a964` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e260` | `0x8000f57c` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f9ac` | `0x8000fb8c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fb8c` | `0x8000fc70` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fc70` | `0x8000fd4c` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fd4c` | `0x8000fde0` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fde0` | `0x8000fe9c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fe9c` | `0x8000ff4c` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000ff4c` | `0x80010030` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010030` | `0x8001006c` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8001006c` | `0x8001019c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001019c` | `0x800102c0` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800102c0` | `0x80010370` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010370` | `0x800104ec` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800104ec` | `0x800105c4` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800105c4` | `0x80010754` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010754` | `0x800108f0` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800108f0` | `0x800109a0` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800109a0` | `0x80010a08` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010a08` | `0x80010aa4` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010aa4` | `0x800110d8` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x800110d8` | `0x800113c0` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800113c0` | `0x80011718` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011718` | `0x80011bf4` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011bf4` | `0x80011e98` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011e98` | `0x80011fb4` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011fb4` | `0x8001226c` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x8001226c` | `0x8001248c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x8001248c` | `0x80012824` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012824` | `0x80012938` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012938` | `0x80012958` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012958` | `0x80012be0` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012be0` | `0x80012cc4` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012cc4` | `0x80012d6c` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012d6c` | `0x800134a0` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800134a0` | `0x80013ad8` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013e14` | `0x80013e28` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013e28` | `0x80013e34` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013e34` | `0x80013e84` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013e84` | `0x80013ea4` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013ea4` | `0x80013f08` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013f08` | `0x800141b0` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800141b0` | `0x80014404` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014404` | `0x800145b8` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800151b8` | `0x800153b0` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800156d0` | `0x80015900` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015cf0` | `0x800187ec` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800187ec` | `0x80019580` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019580` | `0x8001979c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019a84` | `0x80019b18` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a310` | `0x8001a568` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a568` | `0x8001a7e0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a7e0` | `0x8001aa74` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b070` | `0x8001b38c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b754` | `0x8001b9cc` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b9cc` | `0x8001bc70` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bc70` | `0x8001c734` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001ca48` | `0x8001ca90` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d120` | `0x8001d308` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d308` | `0x8001d364` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d364` | `0x8001d430` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d430` | `0x8001d504` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d504` | `0x8001e494` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ed68` | `0x8001ee7c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ee7c` | `0x8001f2b0` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001ff64` | `0x8001ffa4` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020204` | `0x8002034c` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8002034c` | `0x8002037c` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x800208cc` | `0x80020a5c` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021c50` | `0x80021d6c` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021d6c` | `0x80021f30` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021f30` | `0x800221c0` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022894` | `0x800229b4` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800236d0` | `0x800236ec` | 28 | `keccak_init` | UNCONVERTED |
| `0x800236ec` | `0x80023760` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023760` | `0x800237b0` | 80 | `keccak_final` | UNCONVERTED |
| `0x800237b0` | `0x800237dc` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800237dc` | `0x800238bc` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800238bc` | `0x8002393c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x8002393c` | `0x8002396c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023aac` | `0x80023b70` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023b70` | `0x80023bc4` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023bc4` | `0x80023bf4` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023bf4` | `0x80023c34` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023c34` | `0x80023c6c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023c6c` | `0x80023cac` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023e0c` | `0x80023e24` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024de4` | `0x80024fe0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80025078` | `0x80025184` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800251e8` | `0x800253b0` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800253b0` | `0x80025698` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025698` | `0x80025780` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025780` | `0x8002585c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x8002585c` | `0x80025934` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025ce8` | `0x80025e0c` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025e0c` | `0x80025f04` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x8002672c` | `0x8002673c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026920` | `0x80026b38` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026b38` | `0x80026d2c` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800270c0` | `0x80027744` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028660` | `0x80028b7c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028bdc` | `0x80028c7c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800298c8` | `0x8002a0bc` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a750` | `0x8002a9ec` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a9ec` | `0x8002aa24` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c680` | `0x8002cb78` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cb78` | `0x8002d79c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d79c` | `0x8002dd6c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002dd6c` | `0x8002f72c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f72c` | `0x8002f750` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f750` | `0x8002f76c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f76c` | `0x8002fa30` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fa30` | `0x8002fa40` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fa40` | `0x8002fa74` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fa74` | `0x8002fa8c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fa8c` | `0x8002fa9c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fa9c` | `0x8002fad0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fad0` | `0x8002fad8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fad8` | `0x8002fb84` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002fb84` | `0x8002fb90` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002fb90` | `0x8002fbb8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002fbb8` | `0x8002fbf8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002fbf8` | `0x8002fc28` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002fc28` | `0x8002fc28` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002fc28` | `0x8002fc40` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fc40` | `0x8002fc48` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fc48` | `0x8002fc54` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002fc54` | `0x8002fc6c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fc6c` | `0x8002fc84` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fc84` | `0x8002fc98` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002fc98` | `0x8002fcb8` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002fcb8` | `0x8002fccc` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002fccc` | `0x8002fcf8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fcf8` | `0x8002fd40` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fd40` | `0x8002fe20` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fe20` | `0x8002fed0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fed0` | `0x8002fef0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fef0` | `0x8002ff64` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002ff64` | `0x8002ff74` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002ff74` | `0x8002ff80` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002ff80` | `0x80030064` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030064` | `0x8003008c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8003008c` | `0x800300a0` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x800300a0` | `0x800300a0` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x800300a0` | `0x800300a0` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x800300a0` | `0x800300c0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x800300c0` | `0x800300f0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x800300f0` | `0x80030114` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x80030114` | `0x80030134` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x80030134` | `0x80030138` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x80030138` | `0x800301d8` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x800301d8` | `0x800301e8` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x800301e8` | `0x800301f8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800301f8` | `0x80030328` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x80030328` | `0x80030328` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x80030328` | `0x800304c4` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800304c4` | `0x800304c4` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800304c4` | `0x80030524` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x800312dc` | `0x80031304` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031304` | `0x80031514` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031614` | `0x800316c0` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800316c0` | `0x80031744` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031744` | `0x800317c4` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800317c4` | `0x8003187c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x8003187c` | `0x800318f0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800318f0` | `0x80031ab4` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031ab4` | `0x80031b24` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031b24` | `0x80031b9c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031b9c` | `0x80031d4c` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031d4c` | `0x80031dc8` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031dc8` | `0x80031e18` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031e18` | `0x80031e68` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031e68` | `0x80031e98` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031e98` | `0x80031edc` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031edc` | `0x80031f20` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031f20` | `0x80031fd0` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031fd0` | `0x8003212c` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x8003212c` | `0x80032428` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80032428` | `0x80032604` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032604` | `0x800326b0` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800326b0` | `0x80032828` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032828` | `0x800329f4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800329f4` | `0x80032b28` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032c18` | `0x80032cf4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032cf4` | `0x80032e44` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032e44` | `0x80033020` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x800331d0` | `0x800333bc` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800333bc` | `0x80033410` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033410` | `0x80033458` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033458` | `0x8003352c` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x8003352c` | `0x8003360c` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x8003360c` | `0x800337c4` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x800341dc` | `0x80034258` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034258` | `0x80034344` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x800349a8` | `0x80034a18` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034a18` | `0x80034a78` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034e54` | `0x80034ea8` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035070` | `0x800352dc` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800352dc` | `0x8003561c` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x8003561c` | `0x800358cc` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800358cc` | `0x80035c00` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035c00` | `0x80035f88` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035f88` | `0x800360a8` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x800360c8` | `0x800364f8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800364f8` | `0x8003693c` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036990` | `0x80036b3c` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036fb0` | `0x80037174` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037904` | `0x80037bdc` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800384c8` | `0x80038558` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038558` | `0x80038628` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038800` | `0x8003885c` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038a4c` | `0x80038cb8` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038cb8` | `0x80038fd8` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038fd8` | `0x80039288` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039288` | `0x80039464` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039464` | `0x800397ac` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800398f8` | `0x8003b15c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b15c` | `0x8003c398` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c4bc` | `0x8003c5d8` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c5e8` | `0x8003c618` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c618` | `0x8003cbb4` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cbb4` | `0x8003cec4` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cec4` | `0x8003cecc` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cecc` | `0x8003ced0` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003ced0` | `0x8003d0b4` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d1ac` | `0x8003d3f4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d3f4` | `0x8003da58` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003da58` | `0x8003db74` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003db74` | `0x8003dd8c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003dd8c` | `0x8003ddcc` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003ddcc` | `0x8003de14` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003de14` | `0x8003de64` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003de64` | `0x8003debc` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003debc` | `0x8003df1c` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003df1c` | `0x8003df84` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003df84` | `0x8003dff4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dff4` | `0x8003e06c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e06c` | `0x8003e0ec` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e0ec` | `0x8003e174` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e174` | `0x8003e204` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e204` | `0x8003e29c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e29c` | `0x8003e33c` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e33c` | `0x8003e3e4` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e3e4` | `0x8003e494` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e494` | `0x8003e54c` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e54c` | `0x8003e60c` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e60c` | `0x8003e6d4` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e6d4` | `0x8003e7a4` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e7a4` | `0x8003e87c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e87c` | `0x8003e95c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e95c` | `0x8003ea44` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ea44` | `0x8003eb34` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eb34` | `0x8003ec2c` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ec2c` | `0x8003ed2c` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ed2c` | `0x8003ee34` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003ee34` | `0x8003ef44` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ef44` | `0x8003f05c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f05c` | `0x8003f17c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f17c` | `0x8003f2a4` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f2a4` | `0x8003f3d4` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f3d4` | `0x8003f50c` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f50c` | `0x8003f64c` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f64c` | `0x8003f6c4` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f6c4` | `0x8003f73c` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f73c` | `0x8003f7b4` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f7b4` | `0x8003f82c` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f82c` | `0x8003f8a4` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f8a4` | `0x8003f91c` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f91c` | `0x8003f994` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f994` | `0x8003fa0c` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fa0c` | `0x8003fa84` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fa84` | `0x8003fafc` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fafc` | `0x8003fb74` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003fb74` | `0x8003fbec` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003fbec` | `0x8003fc64` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003fc64` | `0x8003fcdc` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003fcdc` | `0x8003fd54` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fd54` | `0x8003fdcc` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fdcc` | `0x8003fe3c` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fe3c` | `0x8003feac` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003feac` | `0x8003ff1c` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003ff1c` | `0x8003ff8c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003ff8c` | `0x8003fffc` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fffc` | `0x8004006c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8004006c` | `0x800400dc` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x800400dc` | `0x8004014c` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8004014c` | `0x800401bc` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x800401bc` | `0x8004022c` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8004022c` | `0x8004029c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004029c` | `0x8004030c` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8004030c` | `0x8004037c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004037c` | `0x800403ec` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800403ec` | `0x8004045c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004045c` | `0x800404cc` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800404cc` | `0x800404e4` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800404e4` | `0x800404f8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800404f8` | `0x80040584` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040584` | `0x8004059c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004059c` | `0x800405b0` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800405b0` | `0x80040638` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040638` | `0x80040650` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040650` | `0x80040664` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040664` | `0x80040684` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040684` | `0x8004068c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004068c` | `0x80040698` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040698` | `0x8004069c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004069c` | `0x80040720` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040720` | `0x800407c8` | 168 | `h_ADD` | UNCONVERTED |
| `0x800407c8` | `0x800408fc` | 308 | `h_MUL` | UNCONVERTED |
| `0x800408fc` | `0x800409a4` | 168 | `h_SUB` | UNCONVERTED |
| `0x800409a4` | `0x80040a9c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040a9c` | `0x80040b34` | 152 | `h_LT` | UNCONVERTED |
| `0x80040b34` | `0x80040bcc` | 152 | `h_GT` | UNCONVERTED |
| `0x80040bcc` | `0x80040c60` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040c60` | `0x80040cf4` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040cf4` | `0x80040d78` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040d78` | `0x80040dd8` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040dd8` | `0x80040e4c` | 116 | `h_AND` | UNCONVERTED |
| `0x80040e4c` | `0x80040ec0` | 116 | `h_OR` | UNCONVERTED |
| `0x80040ec0` | `0x80040f34` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040f34` | `0x80040f94` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040f94` | `0x80041080` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80041080` | `0x80041220` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041220` | `0x800413c0` | 416 | `h_SHR` | UNCONVERTED |
| `0x800413c0` | `0x80041574` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041574` | `0x80041674` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041674` | `0x800416a8` | 52 | `h_POP` | UNCONVERTED |
| `0x800416a8` | `0x800419f4` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800419f4` | `0x80041cd4` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041cd4` | `0x80041df4` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041df4` | `0x80041e38` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041e38` | `0x80041e7c` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041e7c` | `0x80041ecc` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041ecc` | `0x80041f1c` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041f1c` | `0x80041f6c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041f6c` | `0x80041fbc` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041fbc` | `0x8004200c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x8004200c` | `0x8004205c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x8004205c` | `0x800420ac` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800420ac` | `0x800420fc` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800420fc` | `0x8004214c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x8004214c` | `0x8004219c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004219c` | `0x800421ec` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800421ec` | `0x8004223c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x8004223c` | `0x8004228c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004228c` | `0x800422dc` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800422dc` | `0x8004232c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x8004232c` | `0x800423c4` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800423c4` | `0x800424b0` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800424b0` | `0x800424f4` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800424f4` | `0x80042710` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042710` | `0x800428e0` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800428e0` | `0x80042924` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042924` | `0x80042af0` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042af0` | `0x80042af8` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042af8` | `0x80042bb8` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042bb8` | `0x80042cac` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042cac` | `0x80042cf0` | 68 | `h_PC` | UNCONVERTED |
| `0x80042cf0` | `0x80042f78` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042f78` | `0x8004326c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004326c` | `0x80043580` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043580` | `0x800438b4` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800438b4` | `0x80043c08` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043c08` | `0x80043f7c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043f7c` | `0x80044224` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044224` | `0x8004452c` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x8004452c` | `0x80044b98` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044b98` | `0x80045140` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80045140` | `0x800456c0` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800456c0` | `0x80045f4c` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045f4c` | `0x80046038` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80046038` | `0x80046108` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80046108` | `0x80046388` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046388` | `0x80046d20` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046d20` | `0x80047304` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047304` | `0x80047320` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047320` | `0x80048844` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048844` | `0x80048890` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048890` | `0x80048a34` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048a34` | `0x800497fc` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800497fc` | `0x8004baa8` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004baa8` | `0x8004cc20` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cc20` | `0x8004d884` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d884` | `0x8004e68c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e68c` | `0x8004f2f0` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f2f0` | `0x8004fba8` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fba8` | `0x8005049c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005049c` | `0x80050a38` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050a38` | `0x800510e4` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x800510e4` | `0x80051104` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80051104` | `0x800517b0` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x800517b0` | `0x800517d0` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800517d0` | `0x80052100` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052100` | `0x8005244c` | 844 | `h_EXP` | UNCONVERTED |
| `0x8005244c` | `0x800525bc` | 368 | `h_STOP` | UNCONVERTED |
| `0x800525bc` | `0x800525c0` | 4 | `h_invalid` | UNCONVERTED |
| `0x800525c0` | `0x80052648` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80052648` | `0x8005283c` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x8005283c` | `0x8005286c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005286c` | `0x80052880` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052880` | `0x80052890` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052890` | `0x800528c0` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800528c0` | `0x80052ab4` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052ab4` | `0x80052ae4` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052ae4` | `0x80052af8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052af8` | `0x80052b08` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052b08` | `0x80052b38` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052b38` | `0x80052b5c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052b5c` | `0x80052b8c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052b8c` | `0x80052d80` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052d80` | `0x80052db0` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052db0` | `0x80052dc4` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052dc4` | `0x80052dd4` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052dd4` | `0x80052e04` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052e04` | `0x80052ff8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052ff8` | `0x80053028` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80053028` | `0x8005303c` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x8005303c` | `0x8005304c` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x8005304c` | `0x8005307c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005307c` | `0x80053270` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053270` | `0x800532a0` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800532a0` | `0x800532b4` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800532b4` | `0x800532c4` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800532c4` | `0x800532f4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800532f4` | `0x800532f4` | 0 | `.exit_label` | UNCONVERTED |
| `0x800532f4` | `0x80053310` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005349c` | `0x800536d0` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053bd0` | `0x80053d00` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053d00` | `0x80053d5c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053d5c` | `0x80053d7c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053d7c` | `0x80053eb8` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054088` | `0x80054094` | 12 | `requests_hash_verify` | TAIL |
