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

`.text` = [0x80000000, 0x800543c8), 345032 bytes (`RegionMap.textSizeBytes = 0x543c8`)

- symbols in `.text`: 909 (442 converted, 467 unconverted)
- covered by converted `_prog`s: 120568 bytes (34.94%)
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
| `0x8000e594` | `0x8000f8b0` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fce0` | `0x8000fec0` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fec0` | `0x8000ffa4` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000ffa4` | `0x80010080` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x80010080` | `0x80010114` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010114` | `0x800101d0` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x800101d0` | `0x80010280` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x80010280` | `0x80010364` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010364` | `0x800103a0` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103a0` | `0x800104d0` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x800104d0` | `0x800105f4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800105f4` | `0x800106a4` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106a4` | `0x80010820` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010820` | `0x800108f8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800108f8` | `0x80010a88` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010a88` | `0x80010c24` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c24` | `0x80010cd4` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010cd4` | `0x80010d3c` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d3c` | `0x80010dd8` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010dd8` | `0x8001140c` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x8001140c` | `0x800116f4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800116f4` | `0x80011a4c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011a4c` | `0x80011f28` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f28` | `0x800121cc` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800121cc` | `0x800122e8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800122e8` | `0x800125a0` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125a0` | `0x800127c0` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x800127c0` | `0x80012b58` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012b58` | `0x80012c6c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012c6c` | `0x80012c8c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012c8c` | `0x80012f14` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f14` | `0x80012ff8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012ff8` | `0x800130a0` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130a0` | `0x800137d4` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800137d4` | `0x80013e0c` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80014148` | `0x8001415c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x8001415c` | `0x80014168` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80014168` | `0x800141b8` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800141b8` | `0x800141d8` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800141d8` | `0x8001423c` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x8001423c` | `0x800144e4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800144e4` | `0x80014738` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014738` | `0x800148ec` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800154ec` | `0x800156e4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a04` | `0x80015c34` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016024` | `0x80018b20` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80018b20` | `0x800198b4` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x800198b4` | `0x80019ad0` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019db8` | `0x80019e4c` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a644` | `0x8001a89c` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a89c` | `0x8001ab14` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001ab14` | `0x8001ada8` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b3a4` | `0x8001b6c0` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ba88` | `0x8001bd00` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd00` | `0x8001bfa4` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bfa4` | `0x8001ca68` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cd7c` | `0x8001cdc4` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d454` | `0x8001d63c` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d63c` | `0x8001d698` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d698` | `0x8001d764` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d764` | `0x8001d838` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d838` | `0x8001e7c8` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f09c` | `0x8001f1b0` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f1b0` | `0x8001f5e4` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x80020298` | `0x800202d8` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020538` | `0x80020680` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020680` | `0x800206b0` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c00` | `0x80020d90` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021f84` | `0x800220a0` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800220a0` | `0x80022264` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80022264` | `0x800224f4` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022bc8` | `0x80022ce8` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023a04` | `0x80023a20` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a20` | `0x80023a94` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023a94` | `0x80023ae4` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023ae4` | `0x80023b10` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b10` | `0x80023bf0` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023bf0` | `0x80023c70` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023c70` | `0x80023ca0` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023de0` | `0x80023ea4` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023ea4` | `0x80023ef8` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023ef8` | `0x80023f28` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023f28` | `0x80023f68` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023f68` | `0x80023fa0` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023fa0` | `0x80023fe0` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80024140` | `0x80024158` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80025118` | `0x80025314` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800253ac` | `0x800254b8` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x8002551c` | `0x800256e4` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800256e4` | `0x800259cc` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800259cc` | `0x80025ab4` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025ab4` | `0x80025b90` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025b90` | `0x80025c68` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x8002601c` | `0x80026140` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80026140` | `0x80026238` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026a60` | `0x80026a70` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026c54` | `0x80026e6c` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026e6c` | `0x80027060` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800273f4` | `0x80027a78` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028994` | `0x80028eb0` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028f10` | `0x80028fb0` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029bfc` | `0x8002a3f0` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002aa84` | `0x8002ad20` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad20` | `0x8002ad58` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c9b4` | `0x8002ceac` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002ceac` | `0x8002dad0` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002dad0` | `0x8002e0a0` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e0a0` | `0x8002fa60` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fa60` | `0x8002fa84` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fa84` | `0x8002faa0` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002faa0` | `0x8002fd64` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fd64` | `0x8002fd74` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fd74` | `0x8002fda8` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fda8` | `0x8002fdc0` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fdc0` | `0x8002fdd0` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fdd0` | `0x8002fe04` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe04` | `0x8002fe0c` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe0c` | `0x8002feb8` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002feb8` | `0x8002fec4` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002fec4` | `0x8002feec` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002feec` | `0x8002ff2c` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff2c` | `0x8002ff5c` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ff5c` | `0x8002ff5c` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ff5c` | `0x8002ff74` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ff74` | `0x8002ff7c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ff7c` | `0x8002ff88` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002ff88` | `0x8002ffa0` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002ffa0` | `0x8002ffb8` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002ffb8` | `0x8002ffcc` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002ffcc` | `0x8002ffec` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002ffec` | `0x80030000` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030000` | `0x8003002c` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8003002c` | `0x80030074` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x80030074` | `0x80030154` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x80030154` | `0x80030204` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030204` | `0x80030224` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030224` | `0x80030298` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030298` | `0x800302a8` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x800302a8` | `0x800302b4` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x800302b4` | `0x80030398` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030398` | `0x800303c0` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x800303c0` | `0x800303d4` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x800303d4` | `0x800303d4` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x800303d4` | `0x800303d4` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x800303d4` | `0x800303f4` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x800303f4` | `0x80030424` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030424` | `0x80030448` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x80030448` | `0x80030468` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x80030468` | `0x8003046c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8003046c` | `0x8003050c` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8003050c` | `0x8003051c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8003051c` | `0x8003052c` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8003052c` | `0x8003065c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8003065c` | `0x8003065c` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8003065c` | `0x800307f8` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800307f8` | `0x800307f8` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800307f8` | `0x80030858` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031610` | `0x80031638` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031638` | `0x80031848` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031948` | `0x800319f4` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800319f4` | `0x80031a78` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031a78` | `0x80031af8` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031af8` | `0x80031bb0` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031bb0` | `0x80031c24` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c24` | `0x80031de8` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031de8` | `0x80031e58` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031e58` | `0x80031ed0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031ed0` | `0x80032080` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80032080` | `0x800320fc` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x800320fc` | `0x8003214c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x8003214c` | `0x8003219c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x8003219c` | `0x800321cc` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x800321cc` | `0x80032210` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032210` | `0x80032254` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80032254` | `0x80032304` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032304` | `0x80032460` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80032460` | `0x8003275c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003275c` | `0x80032938` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032938` | `0x800329e4` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x800329e4` | `0x80032b5c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032b5c` | `0x80032d28` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d28` | `0x80032e5c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032f4c` | `0x80033028` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80033028` | `0x80033178` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80033178` | `0x80033354` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033504` | `0x800336f0` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x800336f0` | `0x80033744` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033744` | `0x8003378c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8003378c` | `0x80033860` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033860` | `0x80033940` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033940` | `0x80033af8` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034510` | `0x8003458c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x8003458c` | `0x80034678` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034cdc` | `0x80034d4c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034d4c` | `0x80034dac` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80035188` | `0x800351dc` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800353a4` | `0x80035610` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035610` | `0x80035950` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035950` | `0x80035c00` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c00` | `0x80035f34` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035f34` | `0x800362bc` | 904 | `bng2_add` | UNCONVERTED |
| `0x800362bc` | `0x800363dc` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x800363fc` | `0x8003682c` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x8003682c` | `0x80036c70` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036cc4` | `0x80036e70` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x800372e4` | `0x800374a8` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037c38` | `0x80037f10` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800387fc` | `0x8003888c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003888c` | `0x8003895c` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038b34` | `0x80038b90` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038d80` | `0x80038fec` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038fec` | `0x8003930c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003930c` | `0x800395bc` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800395bc` | `0x80039798` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039798` | `0x80039ae0` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c2c` | `0x8003b490` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b490` | `0x8003c6cc` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c7f0` | `0x8003c90c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c91c` | `0x8003c94c` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c94c` | `0x8003cee8` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cee8` | `0x8003d1f8` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d1f8` | `0x8003d200` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d200` | `0x8003d204` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d204` | `0x8003d3e8` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d4e0` | `0x8003d728` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d728` | `0x8003dd8c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003dd8c` | `0x8003dea8` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003dea8` | `0x8003e0c0` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e0c0` | `0x8003e100` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e100` | `0x8003e148` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e148` | `0x8003e198` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e198` | `0x8003e1f0` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e1f0` | `0x8003e250` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e250` | `0x8003e2b8` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e2b8` | `0x8003e328` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e328` | `0x8003e3a0` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e3a0` | `0x8003e420` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e420` | `0x8003e4a8` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e4a8` | `0x8003e538` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e538` | `0x8003e5d0` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e5d0` | `0x8003e670` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e670` | `0x8003e718` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e718` | `0x8003e7c8` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e7c8` | `0x8003e880` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e880` | `0x8003e940` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e940` | `0x8003ea08` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea08` | `0x8003ead8` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003ead8` | `0x8003ebb0` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ebb0` | `0x8003ec90` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ec90` | `0x8003ed78` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ed78` | `0x8003ee68` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003ee68` | `0x8003ef60` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ef60` | `0x8003f060` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f060` | `0x8003f168` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f168` | `0x8003f278` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f278` | `0x8003f390` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f390` | `0x8003f4b0` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f4b0` | `0x8003f5d8` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f5d8` | `0x8003f708` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f708` | `0x8003f840` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f840` | `0x8003f980` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f980` | `0x8003f9f8` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f9f8` | `0x8003fa70` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fa70` | `0x8003fae8` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fae8` | `0x8003fb60` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fb60` | `0x8003fbd8` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fbd8` | `0x8003fc50` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fc50` | `0x8003fcc8` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fcc8` | `0x8003fd40` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fd40` | `0x8003fdb8` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fdb8` | `0x8003fe30` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe30` | `0x8003fea8` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003fea8` | `0x8003ff20` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff20` | `0x8003ff98` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003ff98` | `0x80040010` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040010` | `0x80040088` | 120 | `h_DUP15` | UNCONVERTED |
| `0x80040088` | `0x80040100` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040100` | `0x80040170` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x80040170` | `0x800401e0` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x800401e0` | `0x80040250` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x80040250` | `0x800402c0` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x800402c0` | `0x80040330` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x80040330` | `0x800403a0` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800403a0` | `0x80040410` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040410` | `0x80040480` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x80040480` | `0x800404f0` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x800404f0` | `0x80040560` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x80040560` | `0x800405d0` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x800405d0` | `0x80040640` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040640` | `0x800406b0` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x800406b0` | `0x80040720` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040720` | `0x80040790` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040790` | `0x80040800` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040800` | `0x80040818` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040818` | `0x8004082c` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8004082c` | `0x800408b8` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x800408b8` | `0x800408d0` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800408d0` | `0x800408e4` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x800408e4` | `0x8004096c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8004096c` | `0x80040984` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040984` | `0x80040998` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040998` | `0x800409b8` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x800409b8` | `0x800409c0` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x800409c0` | `0x800409cc` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x800409cc` | `0x800409d0` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800409d0` | `0x80040a54` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040a54` | `0x80040afc` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040afc` | `0x80040c30` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c30` | `0x80040cd8` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040cd8` | `0x80040dd0` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040dd0` | `0x80040e68` | 152 | `h_LT` | UNCONVERTED |
| `0x80040e68` | `0x80040f00` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f00` | `0x80040f94` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040f94` | `0x80041028` | 148 | `h_SGT` | UNCONVERTED |
| `0x80041028` | `0x800410ac` | 132 | `h_EQ` | UNCONVERTED |
| `0x800410ac` | `0x8004110c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004110c` | `0x80041180` | 116 | `h_AND` | UNCONVERTED |
| `0x80041180` | `0x800411f4` | 116 | `h_OR` | UNCONVERTED |
| `0x800411f4` | `0x80041268` | 116 | `h_XOR` | UNCONVERTED |
| `0x80041268` | `0x800412c8` | 96 | `h_NOT` | UNCONVERTED |
| `0x800412c8` | `0x800413b4` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800413b4` | `0x80041554` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041554` | `0x800416f4` | 416 | `h_SHR` | UNCONVERTED |
| `0x800416f4` | `0x800418a8` | 436 | `h_SAR` | UNCONVERTED |
| `0x800418a8` | `0x800419a8` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800419a8` | `0x800419dc` | 52 | `h_POP` | UNCONVERTED |
| `0x800419dc` | `0x80041d28` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d28` | `0x80042008` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042008` | `0x80042128` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80042128` | `0x8004216c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004216c` | `0x800421b0` | 68 | `h_GAS` | UNCONVERTED |
| `0x800421b0` | `0x80042200` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042200` | `0x80042250` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80042250` | `0x800422a0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800422a0` | `0x800422f0` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x800422f0` | `0x80042340` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80042340` | `0x80042390` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80042390` | `0x800423e0` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800423e0` | `0x80042430` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80042430` | `0x80042480` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80042480` | `0x800424d0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800424d0` | `0x80042520` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80042520` | `0x80042570` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042570` | `0x800425c0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x800425c0` | `0x80042610` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042610` | `0x80042660` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042660` | `0x800426f8` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800426f8` | `0x800427e4` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800427e4` | `0x80042828` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042828` | `0x80042a44` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042a44` | `0x80042c14` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c14` | `0x80042c58` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042c58` | `0x80042e24` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e24` | `0x80042e2c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e2c` | `0x80042eec` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042eec` | `0x80042fe0` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042fe0` | `0x80043024` | 68 | `h_PC` | UNCONVERTED |
| `0x80043024` | `0x800432ac` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800432ac` | `0x800435a0` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800435a0` | `0x800438b4` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800438b4` | `0x80043be8` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043be8` | `0x80043f3c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043f3c` | `0x800442b0` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800442b0` | `0x80044558` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044558` | `0x80044860` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044860` | `0x80044ecc` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044ecc` | `0x80045474` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80045474` | `0x800459f4` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x800459f4` | `0x80046280` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80046280` | `0x8004636c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x8004636c` | `0x8004643c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x8004643c` | `0x800466bc` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x800466bc` | `0x80047054` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80047054` | `0x80047638` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047638` | `0x80047654` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047654` | `0x80048b78` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048b78` | `0x80048bc4` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048bc4` | `0x80048d68` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048d68` | `0x80049b30` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b30` | `0x8004bddc` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004bddc` | `0x8004cf54` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cf54` | `0x8004dbb8` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dbb8` | `0x8004e9c0` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e9c0` | `0x8004f624` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f624` | `0x8004fedc` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fedc` | `0x800507d0` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800507d0` | `0x80050d6c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050d6c` | `0x80051418` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051418` | `0x80051438` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80051438` | `0x80051ae4` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051ae4` | `0x80051b04` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b04` | `0x80052434` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052434` | `0x80052780` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052780` | `0x800528f0` | 368 | `h_STOP` | UNCONVERTED |
| `0x800528f0` | `0x800528f4` | 4 | `h_invalid` | UNCONVERTED |
| `0x800528f4` | `0x8005297c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005297c` | `0x80052b70` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052b70` | `0x80052ba0` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052ba0` | `0x80052bb4` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bb4` | `0x80052bc4` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052bc4` | `0x80052bf4` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052bf4` | `0x80052de8` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052de8` | `0x80052e18` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e18` | `0x80052e2c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e2c` | `0x80052e3c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052e3c` | `0x80052e6c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052e6c` | `0x80052e90` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052e90` | `0x80052ec0` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052ec0` | `0x800530b4` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800530b4` | `0x800530e4` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x800530e4` | `0x800530f8` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x800530f8` | `0x80053108` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053108` | `0x80053138` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80053138` | `0x8005332c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005332c` | `0x8005335c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x8005335c` | `0x80053370` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053370` | `0x80053380` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80053380` | `0x800533b0` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800533b0` | `0x800535a4` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800535a4` | `0x800535d4` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800535d4` | `0x800535e8` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800535e8` | `0x800535f8` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x800535f8` | `0x80053628` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053628` | `0x80053628` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053628` | `0x80053644` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800537d0` | `0x80053a04` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053f04` | `0x80054034` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054034` | `0x80054090` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054090` | `0x800540b0` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800540b0` | `0x800541ec` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x800543bc` | `0x800543c8` | 12 | `requests_hash_verify` | TAIL |
