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
not linked** (96 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053e44), 343620 bytes (`RegionMap.textSizeBytes = 0x53e44`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121500 bytes (35.36%)
- NOT covered: 222120 bytes (64.64%), 458 ranges

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
| `0x8000506c` | `0x80005140` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80005140` | `0x80005214` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80005514` | `0x8000555c` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x8000555c` | `0x800055c4` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800055c4` | `0x8000561c` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x8000561c` | `0x80005684` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005684` | `0x80005878` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009b38` | `0x80009cfc` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009cfc` | `0x80009d68` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a624` | `0x8000a824` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a824` | `0x8000a964` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a964` | `0x8000ac20` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000ac20` | `0x8000ad10` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ad10` | `0x8000ae80` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e138` | `0x8000f454` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f884` | `0x8000fa64` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fa64` | `0x8000fb48` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fb48` | `0x8000fc24` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fc24` | `0x8000fcb8` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fcb8` | `0x8000fd74` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fd74` | `0x8000fe24` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fe24` | `0x8000ff08` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000ff08` | `0x8000ff44` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000ff44` | `0x80010074` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x80010074` | `0x80010198` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010198` | `0x80010248` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010248` | `0x800103c4` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800103c4` | `0x8001049c` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8001049c` | `0x8001062c` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8001062c` | `0x800107c8` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800107c8` | `0x80010878` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010878` | `0x800108e0` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x800108e0` | `0x8001097c` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x8001097c` | `0x80010fb0` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010fb0` | `0x80011298` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011298` | `0x800115f0` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x800115f0` | `0x80011acc` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011acc` | `0x80011d70` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011d70` | `0x80011e8c` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011e8c` | `0x80012144` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80012144` | `0x80012364` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012364` | `0x800126fc` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x800126fc` | `0x80012810` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012810` | `0x80012830` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012830` | `0x80012ab8` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012ab8` | `0x80012b9c` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012b9c` | `0x80012c44` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012c44` | `0x80013378` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013378` | `0x800139b0` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013cec` | `0x80013d00` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d00` | `0x80013d0c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013d0c` | `0x80013d5c` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013d5c` | `0x80013d7c` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013d7c` | `0x80013de0` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013de0` | `0x80014088` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014088` | `0x800142dc` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x800142dc` | `0x80014490` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015090` | `0x80015288` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155a8` | `0x800157d8` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015bc8` | `0x800186dc` | 11028 | `block_verdict` | UNCONVERTED |
| `0x800186dc` | `0x80019470` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019470` | `0x8001968c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019974` | `0x80019a08` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a200` | `0x8001a458` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a458` | `0x8001a6d0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a6d0` | `0x8001a964` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001af54` | `0x8001b270` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b638` | `0x8001b8b0` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b8b0` | `0x8001bb54` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb54` | `0x8001c630` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c938` | `0x8001c980` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d010` | `0x8001d1f8` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1f8` | `0x8001d254` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d254` | `0x8001d320` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d320` | `0x8001d3f4` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3f4` | `0x8001e31c` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ebf0` | `0x8001ed04` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ed04` | `0x8001f00c` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fcc0` | `0x8001fd00` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff60` | `0x800200a8` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800200a8` | `0x800200d8` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020628` | `0x800207b8` | 400 | `destroy_storage` | UNCONVERTED |
| `0x800219ac` | `0x80021ac8` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021ac8` | `0x80021c8c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c8c` | `0x80021f1c` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800225f0` | `0x80022710` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023410` | `0x8002342c` | 28 | `keccak_init` | UNCONVERTED |
| `0x8002342c` | `0x800234a0` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800234a0` | `0x800234f0` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234f0` | `0x8002351c` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x8002351c` | `0x800235fc` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800235fc` | `0x8002367c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x8002367c` | `0x800236ac` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237ec` | `0x800238b0` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800238b0` | `0x80023904` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023904` | `0x80023934` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023934` | `0x80023974` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023974` | `0x800239ac` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800239ac` | `0x800239ec` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b4c` | `0x80023b64` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b24` | `0x80024d20` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024db8` | `0x80024ec4` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024f28` | `0x800250f0` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250f0` | `0x800253d8` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800253d8` | `0x800254c0` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800254c0` | `0x8002559c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x8002559c` | `0x80025674` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259f8` | `0x80025b1c` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025b1c` | `0x80025c14` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x8002643c` | `0x8002644c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026630` | `0x80026848` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026848` | `0x80026a3c` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026dd0` | `0x80027454` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028370` | `0x8002888c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288ec` | `0x8002898c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800295d8` | `0x80029dcc` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a460` | `0x8002a6fc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a6fc` | `0x8002a734` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c38c` | `0x8002c884` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c884` | `0x8002d490` | 3084 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d490` | `0x8002da60` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002da60` | `0x8002f420` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f420` | `0x8002f444` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f444` | `0x8002f460` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f460` | `0x8002f724` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f724` | `0x8002f734` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f734` | `0x8002f768` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f768` | `0x8002f780` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f780` | `0x8002f790` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f790` | `0x8002f7c4` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f7c4` | `0x8002f7cc` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f7cc` | `0x8002f878` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f878` | `0x8002f884` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f884` | `0x8002f8ac` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f8ac` | `0x8002f8ec` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f8ec` | `0x8002f91c` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f91c` | `0x8002f91c` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f91c` | `0x8002f934` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f934` | `0x8002f93c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f93c` | `0x8002f948` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f948` | `0x8002f960` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f960` | `0x8002f978` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f978` | `0x8002f98c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f98c` | `0x8002f9ac` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f9ac` | `0x8002f9c0` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f9c0` | `0x8002f9ec` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f9ec` | `0x8002fa34` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fa34` | `0x8002fb14` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fb14` | `0x8002fbc4` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fbc4` | `0x8002fbe4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fbe4` | `0x8002fc58` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fc58` | `0x8002fc68` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc74` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fc74` | `0x8002fd58` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fd58` | `0x8002fd80` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fd80` | `0x8002fd94` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fd94` | `0x8002fd94` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fd94` | `0x8002fd94` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fd94` | `0x8002fdb4` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fdb4` | `0x8002fde4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fde4` | `0x8002fe08` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fe08` | `0x8002fe28` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fe28` | `0x8002fe2c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fe2c` | `0x8002feb8` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002feb8` | `0x8002fec8` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fec8` | `0x8002fed8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fed8` | `0x80030008` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x80030008` | `0x80030008` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x80030008` | `0x800301a4` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x800301a4` | `0x800301a4` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x800301a4` | `0x80030204` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030fbc` | `0x80030fe4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030fe4` | `0x800311f4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800312f4` | `0x800313a0` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800313a0` | `0x80031424` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031424` | `0x800314a4` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800314a4` | `0x8003155c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x8003155c` | `0x800315d0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800315d0` | `0x80031794` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031794` | `0x80031804` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031804` | `0x8003187c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x8003187c` | `0x80031a2c` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031a2c` | `0x80031aa8` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031aa8` | `0x80031af8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031af8` | `0x80031b48` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031b48` | `0x80031b78` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031b78` | `0x80031bbc` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031bbc` | `0x80031c00` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031c00` | `0x80031cb0` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031cb0` | `0x80031e0c` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031e0c` | `0x80032108` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80032108` | `0x800322e4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800322e4` | `0x80032390` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032390` | `0x80032508` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032508` | `0x800326d4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800326d4` | `0x80032808` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800328f8` | `0x800329d4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800329d4` | `0x80032b24` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032b24` | `0x80032d00` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032eb0` | `0x8003309c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003309c` | `0x800330f0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800330f0` | `0x80033138` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033138` | `0x8003320c` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x8003320c` | `0x800332ec` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800332ec` | `0x800334a4` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033ebc` | `0x80033f38` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033f38` | `0x80034024` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034688` | `0x800346f8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800346f8` | `0x80034758` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034b34` | `0x80034b88` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034d50` | `0x80034fbc` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034fbc` | `0x800352fc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800352fc` | `0x800355ac` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800355ac` | `0x800358e0` | 820 | `bng2_double` | UNCONVERTED |
| `0x800358e0` | `0x80035c68` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035c68` | `0x80035d88` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035da8` | `0x800361d8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800361d8` | `0x8003661c` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036670` | `0x8003681c` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036c90` | `0x80036e54` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800375e4` | `0x800378bc` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x800381a8` | `0x80038238` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038238` | `0x80038308` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800384e0` | `0x8003853c` | 92 | `blq_sub` | UNCONVERTED |
| `0x8003872c` | `0x80038998` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038998` | `0x80038cb8` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038cb8` | `0x80038f68` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038f68` | `0x80039144` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039144` | `0x8003948c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800395d8` | `0x8003ae3c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ae3c` | `0x8003c078` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c19c` | `0x8003c2b8` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c2c8` | `0x8003c2f8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c2f8` | `0x8003c894` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c894` | `0x8003cba4` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cba4` | `0x8003cbac` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cbac` | `0x8003cbb0` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cbb0` | `0x8003cd94` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003ce8c` | `0x8003d0d4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d0d4` | `0x8003d738` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d738` | `0x8003d854` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d854` | `0x8003da6c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003da6c` | `0x8003daac` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003daac` | `0x8003daf4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003daf4` | `0x8003db44` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003db44` | `0x8003db9c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003db9c` | `0x8003dbfc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dbfc` | `0x8003dc64` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dc64` | `0x8003dcd4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dcd4` | `0x8003dd4c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dd4c` | `0x8003ddcc` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003ddcc` | `0x8003de54` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003de54` | `0x8003dee4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dee4` | `0x8003df7c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003df7c` | `0x8003e01c` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e01c` | `0x8003e0c4` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e0c4` | `0x8003e174` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e174` | `0x8003e22c` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e22c` | `0x8003e2ec` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e2ec` | `0x8003e3b4` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e3b4` | `0x8003e484` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e484` | `0x8003e55c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e55c` | `0x8003e63c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e63c` | `0x8003e724` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e724` | `0x8003e814` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e814` | `0x8003e90c` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e90c` | `0x8003ea0c` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ea0c` | `0x8003eb14` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003eb14` | `0x8003ec24` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ec24` | `0x8003ed3c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ed3c` | `0x8003ee5c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ee5c` | `0x8003ef84` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ef84` | `0x8003f0b4` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f0b4` | `0x8003f1ec` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f1ec` | `0x8003f32c` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f32c` | `0x8003f3a4` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f3a4` | `0x8003f41c` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f41c` | `0x8003f494` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f494` | `0x8003f50c` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f50c` | `0x8003f584` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f584` | `0x8003f5fc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f5fc` | `0x8003f674` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f674` | `0x8003f6ec` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f6ec` | `0x8003f764` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f764` | `0x8003f7dc` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f7dc` | `0x8003f854` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f854` | `0x8003f8cc` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f8cc` | `0x8003f944` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f944` | `0x8003f9bc` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f9bc` | `0x8003fa34` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fa34` | `0x8003faac` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003faac` | `0x8003fb1c` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fb1c` | `0x8003fb8c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fb8c` | `0x8003fbfc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fbfc` | `0x8003fc6c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fc6c` | `0x8003fcdc` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fcdc` | `0x8003fd4c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fd4c` | `0x8003fdbc` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fdbc` | `0x8003fe2c` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fe2c` | `0x8003fe9c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fe9c` | `0x8003ff0c` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003ff0c` | `0x8003ff7c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003ff7c` | `0x8003ffec` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003ffec` | `0x8004005c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004005c` | `0x800400cc` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800400cc` | `0x8004013c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004013c` | `0x800401ac` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x800401ac` | `0x800401c4` | 24 | `h_DUPN` | UNCONVERTED |
| `0x800401c4` | `0x800401d8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800401d8` | `0x80040264` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040264` | `0x8004027c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004027c` | `0x80040290` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040290` | `0x80040318` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040318` | `0x80040330` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040330` | `0x80040344` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040344` | `0x80040364` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040364` | `0x8004036c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004036c` | `0x80040378` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040378` | `0x8004037c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004037c` | `0x80040400` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040400` | `0x800404a8` | 168 | `h_ADD` | UNCONVERTED |
| `0x800404a8` | `0x800405dc` | 308 | `h_MUL` | UNCONVERTED |
| `0x800405dc` | `0x80040684` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040684` | `0x8004077c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8004077c` | `0x80040814` | 152 | `h_LT` | UNCONVERTED |
| `0x80040814` | `0x800408ac` | 152 | `h_GT` | UNCONVERTED |
| `0x800408ac` | `0x80040940` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040940` | `0x800409d4` | 148 | `h_SGT` | UNCONVERTED |
| `0x800409d4` | `0x80040a58` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040a58` | `0x80040ab8` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040ab8` | `0x80040b2c` | 116 | `h_AND` | UNCONVERTED |
| `0x80040b2c` | `0x80040ba0` | 116 | `h_OR` | UNCONVERTED |
| `0x80040ba0` | `0x80040c14` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040c14` | `0x80040c74` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040c74` | `0x80040d60` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040d60` | `0x80040f00` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040f00` | `0x800410a0` | 416 | `h_SHR` | UNCONVERTED |
| `0x800410a0` | `0x80041254` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041254` | `0x80041354` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041354` | `0x80041388` | 52 | `h_POP` | UNCONVERTED |
| `0x80041388` | `0x80041704` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80041704` | `0x80041a14` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80041a14` | `0x80041b4c` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041b4c` | `0x80041b90` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041b90` | `0x80041bd4` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041bd4` | `0x80041c24` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041c24` | `0x80041c74` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041c74` | `0x80041cc4` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041cc4` | `0x80041d14` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041d14` | `0x80041d64` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041d64` | `0x80041db4` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041db4` | `0x80041e04` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041e04` | `0x80041e54` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041e54` | `0x80041ea4` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041ea4` | `0x80041ef4` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041ef4` | `0x80041f44` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041f44` | `0x80041f94` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041f94` | `0x80041fe4` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041fe4` | `0x80042034` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042034` | `0x80042084` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042084` | `0x8004211c` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x8004211c` | `0x80042208` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042208` | `0x8004224c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004224c` | `0x80042468` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042468` | `0x80042650` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042650` | `0x80042694` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042694` | `0x80042878` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042878` | `0x80042880` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042880` | `0x80042940` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042940` | `0x80042a34` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042a34` | `0x80042a78` | 68 | `h_PC` | UNCONVERTED |
| `0x80042a78` | `0x80042d00` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042d00` | `0x80042ff4` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042ff4` | `0x80043308` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043308` | `0x8004363c` | 820 | `h_LOG2` | UNCONVERTED |
| `0x8004363c` | `0x80043990` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043990` | `0x80043d04` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043d04` | `0x80043fac` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043fac` | `0x800442b4` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800442b4` | `0x80044920` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044920` | `0x80044ee0` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044ee0` | `0x80045460` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045460` | `0x80045cec` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045cec` | `0x80045dd8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045dd8` | `0x80045ea8` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045ea8` | `0x80046140` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80046140` | `0x80046ad0` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046ad0` | `0x800470ac` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x800470ac` | `0x800470c8` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800470c8` | `0x800485ec` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800485ec` | `0x80048638` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048638` | `0x800487f4` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800487f4` | `0x800495bc` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800495bc` | `0x8004b864` | 8872 | `h_CALL` | UNCONVERTED |
| `0x8004b864` | `0x8004c9d8` | 4468 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c9d8` | `0x8004d638` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d638` | `0x8004e440` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e440` | `0x8004f0a0` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f0a0` | `0x8004f958` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f958` | `0x8005024c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005024c` | `0x800507e8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800507e8` | `0x80050e94` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050e94` | `0x80050eb4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050eb4` | `0x80051560` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051560` | `0x80051580` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051580` | `0x80051eb0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051eb0` | `0x800521fc` | 844 | `h_EXP` | UNCONVERTED |
| `0x800521fc` | `0x8005236c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005236c` | `0x80052370` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052370` | `0x800523f8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800523f8` | `0x800525ec` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800525ec` | `0x8005261c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005261c` | `0x80052630` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052630` | `0x80052640` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052640` | `0x80052670` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052670` | `0x80052864` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052864` | `0x80052894` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052894` | `0x800528a8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800528a8` | `0x800528b8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800528b8` | `0x800528e8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800528e8` | `0x8005290c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x8005290c` | `0x8005293c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x8005293c` | `0x80052b30` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052b30` | `0x80052b60` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052b60` | `0x80052b74` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052b74` | `0x80052b84` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052b84` | `0x80052bb4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052bb4` | `0x80052da8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052da8` | `0x80052dd8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052dd8` | `0x80052dec` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052dec` | `0x80052dfc` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052dfc` | `0x80052e2c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052e2c` | `0x80053020` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053020` | `0x80053050` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053050` | `0x80053064` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053064` | `0x80053074` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053074` | `0x800530a4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800530a4` | `0x800530a4` | 0 | `.exit_label` | UNCONVERTED |
| `0x800530a4` | `0x800530c0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005324c` | `0x80053480` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053980` | `0x80053ab0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053ab0` | `0x80053b0c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053b0c` | `0x80053b2c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053b2c` | `0x80053c68` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053e38` | `0x80053e44` | 12 | `requests_hash_verify` | TAIL |
