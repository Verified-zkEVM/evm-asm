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
not linked** (104 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053438), 341048 bytes (`RegionMap.textSizeBytes = 0x53438`)

- symbols in `.text`: 898 (441 converted, 457 unconverted)
- covered by converted `_prog`s: 119072 bytes (34.91%)
- NOT covered: 221976 bytes (65.09%), 458 ranges

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
| `0x8000460c` | `0x800046e0` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x800046e0` | `0x800047b4` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004ab4` | `0x80004afc` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80004afc` | `0x80004b64` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x80004b64` | `0x80004bbc` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x80004bbc` | `0x80004c24` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80004c24` | `0x80004e18` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x800090f4` | `0x800092b8` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x800092b8` | `0x80009324` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x80009be0` | `0x80009de0` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x80009de0` | `0x80009f20` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x80009f20` | `0x8000a1dc` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a1dc` | `0x8000a2cc` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a2cc` | `0x8000a43c` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000d770` | `0x8000ea8c` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000eebc` | `0x8000f09c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f09c` | `0x8000f180` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f180` | `0x8000f25c` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f25c` | `0x8000f2f0` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f2f0` | `0x8000f3ac` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000f3ac` | `0x8000f45c` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000f45c` | `0x8000f540` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000f540` | `0x8000f57c` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000f57c` | `0x8000f6ac` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000f6ac` | `0x8000f7d0` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000f7d0` | `0x8000f880` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000f880` | `0x8000f9fc` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8000f9fc` | `0x8000fad4` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8000fad4` | `0x8000fc64` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8000fc64` | `0x8000fe00` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x8000fe00` | `0x8000feb0` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x8000feb0` | `0x8000ff18` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8000ff18` | `0x8000ffb4` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x8000ffb4` | `0x800105e8` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x800105e8` | `0x800108d0` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800108d0` | `0x80010c28` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80010c28` | `0x80011104` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011104` | `0x800113a8` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800113a8` | `0x800114c4` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800114c4` | `0x8001177c` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x8001177c` | `0x8001199c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x8001199c` | `0x80011d34` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80011d34` | `0x80011e48` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80011e48` | `0x80011e68` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80011e68` | `0x800120f0` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x800120f0` | `0x800121d4` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800121d4` | `0x8001227c` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x8001227c` | `0x800129b0` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800129b0` | `0x80012fe8` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013324` | `0x80013338` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013338` | `0x80013344` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013344` | `0x80013394` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013394` | `0x800133b4` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800133b4` | `0x80013418` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013418` | `0x800136c0` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800136c0` | `0x80013914` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80013914` | `0x80013ac8` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800146c8` | `0x800148c0` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80014be0` | `0x80014e10` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015200` | `0x80017cfc` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80017cfc` | `0x80018a90` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80018a90` | `0x80018cac` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80018f94` | `0x80019028` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019820` | `0x80019a78` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x80019a78` | `0x80019cf0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x80019cf0` | `0x80019f84` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a580` | `0x8001a89c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ac64` | `0x8001aedc` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001aedc` | `0x8001b180` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b180` | `0x8001bc44` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001bf58` | `0x8001bfa0` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c630` | `0x8001c818` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001c818` | `0x8001c874` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001c874` | `0x8001c940` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001c940` | `0x8001ca14` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001ca14` | `0x8001d994` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e268` | `0x8001e37c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e37c` | `0x8001e684` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f338` | `0x8001f378` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f5d8` | `0x8001f720` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001f720` | `0x8001f750` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001fca0` | `0x8001fe30` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021024` | `0x80021140` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021140` | `0x80021304` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021304` | `0x80021594` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021c68` | `0x80021d88` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022a88` | `0x80022aa4` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022aa4` | `0x80022b18` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022b18` | `0x80022b68` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022b68` | `0x80022b94` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022b94` | `0x80022c74` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022c74` | `0x80022cf4` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80022cf4` | `0x80022d24` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80022e64` | `0x80022f28` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80022f28` | `0x80022f7c` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80022f7c` | `0x80022fac` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80022fac` | `0x80022fec` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80022fec` | `0x80023024` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023024` | `0x80023064` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800231c4` | `0x800231dc` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x8002419c` | `0x80024398` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024430` | `0x8002453c` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800245a0` | `0x80024768` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024768` | `0x80024a50` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024a50` | `0x80024b38` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024b38` | `0x80024c14` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024c14` | `0x80024cec` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800250a0` | `0x800251c4` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800251c4` | `0x800252bc` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025ae4` | `0x80025af4` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025cd8` | `0x80025ef0` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80025ef0` | `0x800260e4` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026478` | `0x80026afc` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027a18` | `0x80027f34` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80027f94` | `0x80028034` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028c80` | `0x80029474` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029b08` | `0x80029da4` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029da4` | `0x80029ddc` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ba38` | `0x8002bf30` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002bf30` | `0x8002cb54` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cb54` | `0x8002d124` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d124` | `0x8002eae4` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002eae4` | `0x8002eb08` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002eb08` | `0x8002eb24` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002eb24` | `0x8002ede8` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002ede8` | `0x8002edf8` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002edf8` | `0x8002ee2c` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002ee2c` | `0x8002ee44` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002ee44` | `0x8002ee54` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002ee54` | `0x8002ee88` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002ee88` | `0x8002ee90` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002ee90` | `0x8002ef3c` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ef3c` | `0x8002ef48` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ef48` | `0x8002ef70` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ef70` | `0x8002efb0` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002efb0` | `0x8002efe0` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002efe0` | `0x8002efe0` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002efe0` | `0x8002eff8` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002eff8` | `0x8002f000` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f000` | `0x8002f00c` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f00c` | `0x8002f024` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f024` | `0x8002f03c` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f03c` | `0x8002f050` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f050` | `0x8002f070` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f070` | `0x8002f084` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f084` | `0x8002f0b0` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f0b0` | `0x8002f0f8` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f0f8` | `0x8002f1d8` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f1d8` | `0x8002f288` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f288` | `0x8002f2a8` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f2a8` | `0x8002f31c` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f31c` | `0x8002f32c` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f32c` | `0x8002f338` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f338` | `0x8002f41c` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f41c` | `0x8002f444` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f444` | `0x8002f458` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f458` | `0x8002f458` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f458` | `0x8002f458` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f458` | `0x8002f478` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f478` | `0x8002f4a8` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f4a8` | `0x8002f4cc` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f4cc` | `0x8002f4ec` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f4ec` | `0x8002f4f0` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f4f0` | `0x8002f57c` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f57c` | `0x8002f58c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f58c` | `0x8002f59c` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f59c` | `0x8002f6cc` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f6cc` | `0x8002f6cc` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f6cc` | `0x8002f868` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002f868` | `0x8002f868` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002f868` | `0x8002f8c8` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030680` | `0x800306a8` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800306a8` | `0x800308b8` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800309b8` | `0x80030a64` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030a64` | `0x80030ae8` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030ae8` | `0x80030b68` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030b68` | `0x80030c20` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030c20` | `0x80030c94` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030c94` | `0x80030e58` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80030e58` | `0x80030ec8` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80030ec8` | `0x80030f40` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80030f40` | `0x800310f0` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800310f0` | `0x8003116c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003116c` | `0x800311bc` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800311bc` | `0x8003120c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x8003120c` | `0x8003123c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x8003123c` | `0x80031280` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031280` | `0x800312c4` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800312c4` | `0x80031374` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031374` | `0x800314d0` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800314d0` | `0x800317cc` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800317cc` | `0x800319a8` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800319a8` | `0x80031a54` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031a54` | `0x80031bcc` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031bcc` | `0x80031d98` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031d98` | `0x80031ecc` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80031fbc` | `0x80032098` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032098` | `0x800321e8` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800321e8` | `0x800323c4` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032574` | `0x80032760` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032760` | `0x800327b4` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800327b4` | `0x800327fc` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800327fc` | `0x800328d0` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800328d0` | `0x800329b0` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800329b0` | `0x80032b68` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033580` | `0x800335fc` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800335fc` | `0x800336e8` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033d4c` | `0x80033dbc` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033dbc` | `0x80033e1c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800341f8` | `0x8003424c` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034414` | `0x80034680` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034680` | `0x800349c0` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800349c0` | `0x80034c70` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034c70` | `0x80034fa4` | 820 | `bng2_double` | UNCONVERTED |
| `0x80034fa4` | `0x8003532c` | 904 | `bng2_add` | UNCONVERTED |
| `0x8003532c` | `0x8003544c` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x8003546c` | `0x8003589c` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x8003589c` | `0x80035ce0` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035d34` | `0x80035ee0` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036354` | `0x80036518` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036ca8` | `0x80036f80` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003786c` | `0x800378fc` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800378fc` | `0x800379cc` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037ba4` | `0x80037c00` | 92 | `blq_sub` | UNCONVERTED |
| `0x80037df0` | `0x8003805c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003805c` | `0x8003837c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003837c` | `0x8003862c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003862c` | `0x80038808` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038808` | `0x80038b50` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038c9c` | `0x8003a500` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a500` | `0x8003b73c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003b860` | `0x8003b97c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003b98c` | `0x8003b9bc` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003b9bc` | `0x8003bf58` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003bf58` | `0x8003c268` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c268` | `0x8003c270` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c270` | `0x8003c274` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c274` | `0x8003c458` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c550` | `0x8003c798` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c798` | `0x8003cdfc` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003cdfc` | `0x8003cf18` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003cf18` | `0x8003d130` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d130` | `0x8003d170` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d170` | `0x8003d1b8` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d1b8` | `0x8003d208` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d208` | `0x8003d260` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d260` | `0x8003d2c0` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d2c0` | `0x8003d328` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d328` | `0x8003d398` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d398` | `0x8003d410` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d410` | `0x8003d490` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d490` | `0x8003d518` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d518` | `0x8003d5a8` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d5a8` | `0x8003d640` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d640` | `0x8003d6e0` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d6e0` | `0x8003d788` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d788` | `0x8003d838` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003d838` | `0x8003d8f0` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003d8f0` | `0x8003d9b0` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003d9b0` | `0x8003da78` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003da78` | `0x8003db48` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003db48` | `0x8003dc20` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003dc20` | `0x8003dd00` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003dd00` | `0x8003dde8` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003dde8` | `0x8003ded8` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003ded8` | `0x8003dfd0` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003dfd0` | `0x8003e0d0` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e0d0` | `0x8003e1d8` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e1d8` | `0x8003e2e8` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e2e8` | `0x8003e400` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e400` | `0x8003e520` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e520` | `0x8003e648` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e648` | `0x8003e778` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e778` | `0x8003e8b0` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003e8b0` | `0x8003e9f0` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003e9f0` | `0x8003ea68` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ea68` | `0x8003eae0` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003eae0` | `0x8003eb58` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003eb58` | `0x8003ebd0` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ebd0` | `0x8003ec48` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ec48` | `0x8003ecc0` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003ecc0` | `0x8003ed38` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ed38` | `0x8003edb0` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003edb0` | `0x8003ee28` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003ee28` | `0x8003eea0` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003eea0` | `0x8003ef18` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ef18` | `0x8003ef90` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ef90` | `0x8003f008` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f008` | `0x8003f080` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f080` | `0x8003f0f8` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f0f8` | `0x8003f170` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f170` | `0x8003f1e0` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f1e0` | `0x8003f250` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f250` | `0x8003f2c0` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f2c0` | `0x8003f330` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f330` | `0x8003f3a0` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f3a0` | `0x8003f410` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f410` | `0x8003f480` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f480` | `0x8003f4f0` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f4f0` | `0x8003f560` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f560` | `0x8003f5d0` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f5d0` | `0x8003f640` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f640` | `0x8003f6b0` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f6b0` | `0x8003f720` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f720` | `0x8003f790` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f790` | `0x8003f800` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003f800` | `0x8003f870` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003f870` | `0x8003f888` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003f888` | `0x8003f89c` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003f89c` | `0x8003f928` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003f928` | `0x8003f940` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003f940` | `0x8003f954` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003f954` | `0x8003f9dc` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003f9dc` | `0x8003f9f4` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003f9f4` | `0x8003fa08` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003fa08` | `0x8003fa28` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003fa28` | `0x8003fa30` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003fa30` | `0x8003fa3c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003fa3c` | `0x8003fa40` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003fa40` | `0x8003fac4` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fac4` | `0x8003fb6c` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fb6c` | `0x8003fca0` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fca0` | `0x8003fd48` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003fd48` | `0x8003fe40` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003fe40` | `0x8003fed8` | 152 | `h_LT` | UNCONVERTED |
| `0x8003fed8` | `0x8003ff70` | 152 | `h_GT` | UNCONVERTED |
| `0x8003ff70` | `0x80040004` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040004` | `0x80040098` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040098` | `0x8004011c` | 132 | `h_EQ` | UNCONVERTED |
| `0x8004011c` | `0x8004017c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004017c` | `0x800401f0` | 116 | `h_AND` | UNCONVERTED |
| `0x800401f0` | `0x80040264` | 116 | `h_OR` | UNCONVERTED |
| `0x80040264` | `0x800402d8` | 116 | `h_XOR` | UNCONVERTED |
| `0x800402d8` | `0x80040338` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040338` | `0x80040424` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040424` | `0x800405c4` | 416 | `h_SHL` | UNCONVERTED |
| `0x800405c4` | `0x80040764` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040764` | `0x80040918` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040918` | `0x80040a18` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040a18` | `0x80040a4c` | 52 | `h_POP` | UNCONVERTED |
| `0x80040a4c` | `0x80040d98` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80040d98` | `0x80041078` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041078` | `0x80041198` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041198` | `0x800411dc` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800411dc` | `0x80041220` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041220` | `0x80041270` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041270` | `0x800412c0` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800412c0` | `0x80041310` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041310` | `0x80041360` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041360` | `0x800413b0` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800413b0` | `0x80041400` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041400` | `0x80041450` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041450` | `0x800414a0` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800414a0` | `0x800414f0` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800414f0` | `0x80041540` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041540` | `0x80041590` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041590` | `0x800415e0` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800415e0` | `0x80041630` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041630` | `0x80041680` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041680` | `0x800416d0` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800416d0` | `0x80041768` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041768` | `0x80041854` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041854` | `0x80041898` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041898` | `0x80041ab4` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041ab4` | `0x80041c84` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041c84` | `0x80041cc8` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041cc8` | `0x80041e94` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80041e94` | `0x80041e9c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80041e9c` | `0x80041f5c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80041f5c` | `0x80042050` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042050` | `0x80042094` | 68 | `h_PC` | UNCONVERTED |
| `0x80042094` | `0x8004231c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x8004231c` | `0x80042610` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042610` | `0x80042924` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042924` | `0x80042c58` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042c58` | `0x80042fac` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80042fac` | `0x80043320` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043320` | `0x800435c8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800435c8` | `0x800438d0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800438d0` | `0x80043f3c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80043f3c` | `0x800444e4` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800444e4` | `0x80044a64` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044a64` | `0x800452f0` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800452f0` | `0x800453dc` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800453dc` | `0x800454ac` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800454ac` | `0x8004572c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x8004572c` | `0x800460c4` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800460c4` | `0x800466a8` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800466a8` | `0x800466c4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800466c4` | `0x80047be8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047be8` | `0x80047c34` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047c34` | `0x80047dd8` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047dd8` | `0x80048ba0` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048ba0` | `0x8004ae4c` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004ae4c` | `0x8004bfc4` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004bfc4` | `0x8004cc28` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004cc28` | `0x8004da30` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004da30` | `0x8004e694` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e694` | `0x8004ef4c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ef4c` | `0x8004f840` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004f840` | `0x8004fddc` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fddc` | `0x80050488` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050488` | `0x800504a8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800504a8` | `0x80050b54` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050b54` | `0x80050b74` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050b74` | `0x800514a4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800514a4` | `0x800517f0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800517f0` | `0x80051960` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051960` | `0x80051964` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051964` | `0x800519ec` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800519ec` | `0x80051be0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051be0` | `0x80051c10` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051c10` | `0x80051c24` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051c24` | `0x80051c34` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051c34` | `0x80051c64` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051c64` | `0x80051e58` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80051e58` | `0x80051e88` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80051e88` | `0x80051e9c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80051e9c` | `0x80051eac` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80051eac` | `0x80051edc` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80051edc` | `0x80051f00` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80051f00` | `0x80051f30` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80051f30` | `0x80052124` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052124` | `0x80052154` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052154` | `0x80052168` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052168` | `0x80052178` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052178` | `0x800521a8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800521a8` | `0x8005239c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005239c` | `0x800523cc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800523cc` | `0x800523e0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800523e0` | `0x800523f0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800523f0` | `0x80052420` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052420` | `0x80052614` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052614` | `0x80052644` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052644` | `0x80052658` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052658` | `0x80052668` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052668` | `0x80052698` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052698` | `0x80052698` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052698` | `0x800526b4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052840` | `0x80052a74` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80052f74` | `0x800530a4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800530a4` | `0x80053100` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053100` | `0x80053120` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053120` | `0x8005325c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x8005342c` | `0x80053438` | 12 | `requests_hash_verify` | TAIL |
