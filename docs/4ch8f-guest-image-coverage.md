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

`.text` = [0x80000000, 0x80054424), 345124 bytes (`RegionMap.textSizeBytes = 0x54424`)

- symbols in `.text`: 909 (442 converted, 467 unconverted)
- covered by converted `_prog`s: 120644 bytes (34.96%)
- NOT covered: 224480 bytes (65.04%), 468 ranges

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
| `0x8000998c` | `0x80009b50` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009b50` | `0x80009bbc` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a478` | `0x8000a678` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a678` | `0x8000a7b8` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a7b8` | `0x8000aa74` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000aa74` | `0x8000ab64` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ab64` | `0x8000acd4` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e5d0` | `0x8000f8ec` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fd1c` | `0x8000fefc` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fefc` | `0x8000ffe0` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000ffe0` | `0x800100bc` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x800100bc` | `0x80010150` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010150` | `0x8001020c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8001020c` | `0x800102bc` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x800102bc` | `0x800103a0` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x800103a0` | `0x800103dc` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103dc` | `0x8001050c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001050c` | `0x80010630` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010630` | `0x800106e0` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106e0` | `0x8001085c` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8001085c` | `0x80010934` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010934` | `0x80010ac4` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010ac4` | `0x80010c60` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c60` | `0x80010d10` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010d10` | `0x80010d78` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d78` | `0x80010e14` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010e14` | `0x80011448` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011448` | `0x80011730` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011730` | `0x80011a88` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011a88` | `0x80011f64` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f64` | `0x80012208` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80012208` | `0x80012324` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80012324` | `0x800125dc` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125dc` | `0x800127fc` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800127fc` | `0x80012b94` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012b94` | `0x80012ca8` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012ca8` | `0x80012cc8` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012cc8` | `0x80012f50` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f50` | `0x80013034` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80013034` | `0x800130dc` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130dc` | `0x80013810` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013810` | `0x80013e48` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80014184` | `0x80014198` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80014198` | `0x800141a4` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800141a4` | `0x800141f4` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800141f4` | `0x80014214` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80014214` | `0x80014278` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014278` | `0x80014520` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014520` | `0x80014774` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014774` | `0x80014928` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015528` | `0x80015720` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a40` | `0x80015c70` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016060` | `0x80018b6c` | 11020 | `block_verdict` | UNCONVERTED |
| `0x80018b6c` | `0x80019900` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019900` | `0x80019b1c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019e04` | `0x80019e98` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a690` | `0x8001a8e8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a8e8` | `0x8001ab60` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001ab60` | `0x8001adf4` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b3f0` | `0x8001b70c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001bad4` | `0x8001bd4c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd4c` | `0x8001bff0` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bff0` | `0x8001cab4` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cdc8` | `0x8001ce10` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d4b0` | `0x8001d698` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d698` | `0x8001d6f4` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d6f4` | `0x8001d7c0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7c0` | `0x8001d894` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d894` | `0x8001e824` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f0f8` | `0x8001f20c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f20c` | `0x8001f640` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x800202f4` | `0x80020334` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020594` | `0x800206dc` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800206dc` | `0x8002070c` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c5c` | `0x80020dec` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021fe0` | `0x800220fc` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800220fc` | `0x800222c0` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x800222c0` | `0x80022550` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022c24` | `0x80022d44` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023a60` | `0x80023a7c` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a7c` | `0x80023af0` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023af0` | `0x80023b40` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b40` | `0x80023b6c` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b6c` | `0x80023c4c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c4c` | `0x80023ccc` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023ccc` | `0x80023cfc` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023e3c` | `0x80023f00` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023f00` | `0x80023f54` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f54` | `0x80023f84` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023f84` | `0x80023fc4` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023fc4` | `0x80023ffc` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023ffc` | `0x8002403c` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x8002419c` | `0x800241b4` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80025174` | `0x80025370` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80025408` | `0x80025514` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025578` | `0x80025740` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80025740` | `0x80025a28` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025a28` | `0x80025b10` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025b10` | `0x80025bec` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025bec` | `0x80025cc4` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80026078` | `0x8002619c` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x8002619c` | `0x80026294` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026abc` | `0x80026acc` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026cb0` | `0x80026ec8` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026ec8` | `0x800270bc` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80027450` | `0x80027ad4` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800289f0` | `0x80028f0c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028f6c` | `0x8002900c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029c58` | `0x8002a44c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002aae0` | `0x8002ad7c` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad7c` | `0x8002adb4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ca10` | `0x8002cf08` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cf08` | `0x8002db2c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db2c` | `0x8002e0fc` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e0fc` | `0x8002fabc` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fabc` | `0x8002fae0` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fae0` | `0x8002fafc` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fafc` | `0x8002fdc0` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fdc0` | `0x8002fdd0` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fdd0` | `0x8002fe04` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fe04` | `0x8002fe1c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe1c` | `0x8002fe2c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe2c` | `0x8002fe60` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe60` | `0x8002fe68` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe68` | `0x8002ff14` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ff14` | `0x8002ff20` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff20` | `0x8002ff48` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff48` | `0x8002ff88` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff88` | `0x8002ffb8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffb8` | `0x8002ffb8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffb8` | `0x8002ffd0` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ffd0` | `0x8002ffd8` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ffd8` | `0x8002ffe4` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002ffe4` | `0x8002fffc` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fffc` | `0x80030014` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030014` | `0x80030028` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030028` | `0x80030048` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030048` | `0x8003005c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8003005c` | `0x80030088` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x80030088` | `0x800300d0` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300d0` | `0x800301b0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x800301b0` | `0x80030260` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030260` | `0x80030280` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030280` | `0x800302f4` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x800302f4` | `0x80030304` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030304` | `0x80030310` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x80030310` | `0x800303f4` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x800303f4` | `0x8003041c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8003041c` | `0x80030430` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030430` | `0x80030430` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030430` | `0x80030430` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030430` | `0x80030450` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030450` | `0x80030480` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030480` | `0x800304a4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x800304a4` | `0x800304c4` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304c4` | `0x800304c8` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304c8` | `0x80030568` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030568` | `0x80030578` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030578` | `0x80030588` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x80030588` | `0x800306b8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306b8` | `0x800306b8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306b8` | `0x80030854` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030854` | `0x80030854` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030854` | `0x800308b4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8003166c` | `0x80031694` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031694` | `0x800318a4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800319a4` | `0x80031a50` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a50` | `0x80031ad4` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031ad4` | `0x80031b54` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031b54` | `0x80031c0c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031c0c` | `0x80031c80` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c80` | `0x80031e44` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e44` | `0x80031eb4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031eb4` | `0x80031f2c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f2c` | `0x800320dc` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320dc` | `0x80032158` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032158` | `0x800321a8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800321a8` | `0x800321f8` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800321f8` | `0x80032228` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032228` | `0x8003226c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x8003226c` | `0x800322b0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800322b0` | `0x80032360` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032360` | `0x800324bc` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324bc` | `0x800327b8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327b8` | `0x80032994` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032994` | `0x80032a40` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a40` | `0x80032bb8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032bb8` | `0x80032d84` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d84` | `0x80032eb8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032fa8` | `0x80033084` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80033084` | `0x800331d4` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331d4` | `0x800333b0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033560` | `0x8003374c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003374c` | `0x800337a0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800337a0` | `0x800337e8` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800337e8` | `0x800338bc` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338bc` | `0x8003399c` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x8003399c` | `0x80033b54` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x8003456c` | `0x800345e8` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800345e8` | `0x800346d4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d38` | `0x80034da8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034da8` | `0x80034e08` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800351e4` | `0x80035238` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035400` | `0x8003566c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x8003566c` | `0x800359ac` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800359ac` | `0x80035c5c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c5c` | `0x80035f90` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035f90` | `0x80036318` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036318` | `0x80036438` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036458` | `0x80036888` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80036888` | `0x80036ccc` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d20` | `0x80036ecc` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037340` | `0x80037504` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037c94` | `0x80037f6c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038858` | `0x800388e8` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800388e8` | `0x800389b8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038b90` | `0x80038bec` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038ddc` | `0x80039048` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039048` | `0x80039368` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039368` | `0x80039618` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039618` | `0x800397f4` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800397f4` | `0x80039b3c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c88` | `0x8003b4ec` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b4ec` | `0x8003c728` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c84c` | `0x8003c968` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c978` | `0x8003c9a8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c9a8` | `0x8003cf44` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf44` | `0x8003d254` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d254` | `0x8003d25c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d25c` | `0x8003d260` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d260` | `0x8003d444` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d53c` | `0x8003d784` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d784` | `0x8003dde8` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003dde8` | `0x8003df04` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003df04` | `0x8003e11c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e11c` | `0x8003e15c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e15c` | `0x8003e1a4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e1a4` | `0x8003e1f4` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e1f4` | `0x8003e24c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e24c` | `0x8003e2ac` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e2ac` | `0x8003e314` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e314` | `0x8003e384` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e384` | `0x8003e3fc` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e3fc` | `0x8003e47c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e47c` | `0x8003e504` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e504` | `0x8003e594` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e594` | `0x8003e62c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e62c` | `0x8003e6cc` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6cc` | `0x8003e774` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e774` | `0x8003e824` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e824` | `0x8003e8dc` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8dc` | `0x8003e99c` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e99c` | `0x8003ea64` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea64` | `0x8003eb34` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb34` | `0x8003ec0c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ec0c` | `0x8003ecec` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ecec` | `0x8003edd4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003edd4` | `0x8003eec4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eec4` | `0x8003efbc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efbc` | `0x8003f0bc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0bc` | `0x8003f1c4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1c4` | `0x8003f2d4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2d4` | `0x8003f3ec` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f3ec` | `0x8003f50c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f50c` | `0x8003f634` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f634` | `0x8003f764` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f764` | `0x8003f89c` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f89c` | `0x8003f9dc` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9dc` | `0x8003fa54` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa54` | `0x8003facc` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003facc` | `0x8003fb44` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb44` | `0x8003fbbc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fbbc` | `0x8003fc34` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc34` | `0x8003fcac` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fcac` | `0x8003fd24` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd24` | `0x8003fd9c` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fd9c` | `0x8003fe14` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fe14` | `0x8003fe8c` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe8c` | `0x8003ff04` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ff04` | `0x8003ff7c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff7c` | `0x8003fff4` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003fff4` | `0x8004006c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8004006c` | `0x800400e4` | 120 | `h_DUP15` | UNCONVERTED |
| `0x800400e4` | `0x8004015c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8004015c` | `0x800401cc` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401cc` | `0x8004023c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8004023c` | `0x800402ac` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800402ac` | `0x8004031c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8004031c` | `0x8004038c` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8004038c` | `0x800403fc` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800403fc` | `0x8004046c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8004046c` | `0x800404dc` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404dc` | `0x8004054c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8004054c` | `0x800405bc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405bc` | `0x8004062c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004062c` | `0x8004069c` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8004069c` | `0x8004070c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004070c` | `0x8004077c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004077c` | `0x800407ec` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800407ec` | `0x8004085c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004085c` | `0x80040874` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040874` | `0x80040888` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80040888` | `0x80040914` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040914` | `0x8004092c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004092c` | `0x80040940` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040940` | `0x800409c8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409c8` | `0x800409e0` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800409e0` | `0x800409f4` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800409f4` | `0x80040a14` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040a14` | `0x80040a1c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a1c` | `0x80040a28` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a28` | `0x80040a2c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a2c` | `0x80040ab0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040ab0` | `0x80040b58` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b58` | `0x80040c8c` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c8c` | `0x80040d34` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d34` | `0x80040e2c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e2c` | `0x80040ec4` | 152 | `h_LT` | UNCONVERTED |
| `0x80040ec4` | `0x80040f5c` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f5c` | `0x80040ff0` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040ff0` | `0x80041084` | 148 | `h_SGT` | UNCONVERTED |
| `0x80041084` | `0x80041108` | 132 | `h_EQ` | UNCONVERTED |
| `0x80041108` | `0x80041168` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041168` | `0x800411dc` | 116 | `h_AND` | UNCONVERTED |
| `0x800411dc` | `0x80041250` | 116 | `h_OR` | UNCONVERTED |
| `0x80041250` | `0x800412c4` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412c4` | `0x80041324` | 96 | `h_NOT` | UNCONVERTED |
| `0x80041324` | `0x80041410` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80041410` | `0x800415b0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800415b0` | `0x80041750` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041750` | `0x80041904` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041904` | `0x80041a04` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041a04` | `0x80041a38` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a38` | `0x80041d84` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d84` | `0x80042064` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042064` | `0x80042184` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80042184` | `0x800421c8` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421c8` | `0x8004220c` | 68 | `h_GAS` | UNCONVERTED |
| `0x8004220c` | `0x8004225c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x8004225c` | `0x800422ac` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800422ac` | `0x800422fc` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800422fc` | `0x8004234c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8004234c` | `0x8004239c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x8004239c` | `0x800423ec` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800423ec` | `0x8004243c` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x8004243c` | `0x8004248c` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x8004248c` | `0x800424dc` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424dc` | `0x8004252c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004252c` | `0x8004257c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x8004257c` | `0x800425cc` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425cc` | `0x8004261c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004261c` | `0x8004266c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x8004266c` | `0x800426bc` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426bc` | `0x80042754` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042754` | `0x80042840` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042840` | `0x80042884` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042884` | `0x80042aa0` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042aa0` | `0x80042c70` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c70` | `0x80042cb4` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042cb4` | `0x80042e80` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e80` | `0x80042e88` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e88` | `0x80042f48` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f48` | `0x8004303c` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x8004303c` | `0x80043080` | 68 | `h_PC` | UNCONVERTED |
| `0x80043080` | `0x80043308` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80043308` | `0x800435fc` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800435fc` | `0x80043910` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043910` | `0x80043c44` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c44` | `0x80043f98` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043f98` | `0x8004430c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x8004430c` | `0x800445b4` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800445b4` | `0x800448bc` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448bc` | `0x80044f28` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f28` | `0x800454d0` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454d0` | `0x80045a50` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a50` | `0x800462dc` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462dc` | `0x800463c8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463c8` | `0x80046498` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80046498` | `0x80046718` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046718` | `0x800470b0` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800470b0` | `0x80047694` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047694` | `0x800476b0` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800476b0` | `0x80048bd4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048bd4` | `0x80048c20` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c20` | `0x80048dc4` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048dc4` | `0x80049b8c` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b8c` | `0x8004be38` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be38` | `0x8004cfb0` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cfb0` | `0x8004dc14` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dc14` | `0x8004ea1c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea1c` | `0x8004f680` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f680` | `0x8004ff38` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff38` | `0x8005082c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005082c` | `0x80050dc8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050dc8` | `0x80051474` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051474` | `0x80051494` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80051494` | `0x80051b40` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b40` | `0x80051b60` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b60` | `0x80052490` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052490` | `0x800527dc` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527dc` | `0x8005294c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005294c` | `0x80052950` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052950` | `0x800529d8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529d8` | `0x80052bcc` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052bcc` | `0x80052bfc` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052bfc` | `0x80052c10` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c10` | `0x80052c20` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c20` | `0x80052c50` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c50` | `0x80052e44` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e44` | `0x80052e74` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e74` | `0x80052e88` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e88` | `0x80052e98` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052e98` | `0x80052ec8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052ec8` | `0x80052eec` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052eec` | `0x80052f1c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f1c` | `0x80053110` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80053110` | `0x80053140` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053140` | `0x80053154` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053154` | `0x80053164` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053164` | `0x80053194` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80053194` | `0x80053388` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80053388` | `0x800533b8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533b8` | `0x800533cc` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533cc` | `0x800533dc` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533dc` | `0x8005340c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005340c` | `0x80053600` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053600` | `0x80053630` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053630` | `0x80053644` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053644` | `0x80053654` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053654` | `0x80053684` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053684` | `0x80053684` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053684` | `0x800536a0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005382c` | `0x80053a60` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053f60` | `0x80054090` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054090` | `0x800540ec` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800540ec` | `0x8005410c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005410c` | `0x80054248` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054418` | `0x80054424` | 12 | `requests_hash_verify` | TAIL |
