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
not linked** (104 of 547 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053650), 341584 bytes (`RegionMap.textSizeBytes = 0x53650`)

- symbols in `.text`: 900 (443 converted, 457 unconverted)
- covered by converted `_prog`s: 119608 bytes (35.02%)
- NOT covered: 221976 bytes (64.98%), 458 ranges

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
| `0x8000d988` | `0x8000eca4` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f0d4` | `0x8000f2b4` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f2b4` | `0x8000f398` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f398` | `0x8000f474` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f474` | `0x8000f508` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f508` | `0x8000f5c4` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000f5c4` | `0x8000f674` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000f674` | `0x8000f758` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000f758` | `0x8000f794` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000f794` | `0x8000f8c4` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000f8c4` | `0x8000f9e8` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000f9e8` | `0x8000fa98` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000fa98` | `0x8000fc14` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8000fc14` | `0x8000fcec` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8000fcec` | `0x8000fe7c` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8000fe7c` | `0x80010018` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010018` | `0x800100c8` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800100c8` | `0x80010130` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010130` | `0x800101cc` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800101cc` | `0x80010800` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010800` | `0x80010ae8` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010ae8` | `0x80010e40` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80010e40` | `0x8001131c` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x8001131c` | `0x800115c0` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800115c0` | `0x800116dc` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800116dc` | `0x80011994` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80011994` | `0x80011bb4` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80011bb4` | `0x80011f4c` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80011f4c` | `0x80012060` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012060` | `0x80012080` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012080` | `0x80012308` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012308` | `0x800123ec` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x800123ec` | `0x80012494` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012494` | `0x80012bc8` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80012bc8` | `0x80013200` | 1592 | `block_state_root` | UNCONVERTED |
| `0x8001353c` | `0x80013550` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013550` | `0x8001355c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x8001355c` | `0x800135ac` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800135ac` | `0x800135cc` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800135cc` | `0x80013630` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013630` | `0x800138d8` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800138d8` | `0x80013b2c` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80013b2c` | `0x80013ce0` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800148e0` | `0x80014ad8` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80014df8` | `0x80015028` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015418` | `0x80017f14` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80017f14` | `0x80018ca8` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80018ca8` | `0x80018ec4` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800191ac` | `0x80019240` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019a38` | `0x80019c90` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x80019c90` | `0x80019f08` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x80019f08` | `0x8001a19c` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a798` | `0x8001aab4` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ae7c` | `0x8001b0f4` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b0f4` | `0x8001b398` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b398` | `0x8001be5c` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c170` | `0x8001c1b8` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c848` | `0x8001ca30` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001ca30` | `0x8001ca8c` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001ca8c` | `0x8001cb58` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001cb58` | `0x8001cc2c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cc2c` | `0x8001dbac` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e480` | `0x8001e594` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e594` | `0x8001e89c` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f550` | `0x8001f590` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f7f0` | `0x8001f938` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001f938` | `0x8001f968` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001feb8` | `0x80020048` | 400 | `destroy_storage` | UNCONVERTED |
| `0x8002123c` | `0x80021358` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021358` | `0x8002151c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x8002151c` | `0x800217ac` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021e80` | `0x80021fa0` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022ca0` | `0x80022cbc` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022cbc` | `0x80022d30` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022d30` | `0x80022d80` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022d80` | `0x80022dac` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022dac` | `0x80022e8c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022e8c` | `0x80022f0c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80022f0c` | `0x80022f3c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x8002307c` | `0x80023140` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023140` | `0x80023194` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023194` | `0x800231c4` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800231c4` | `0x80023204` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023204` | `0x8002323c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002323c` | `0x8002327c` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800233dc` | `0x800233f4` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800243b4` | `0x800245b0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024648` | `0x80024754` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800247b8` | `0x80024980` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024980` | `0x80024c68` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024c68` | `0x80024d50` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024d50` | `0x80024e2c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024e2c` | `0x80024f04` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800252b8` | `0x800253dc` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800253dc` | `0x800254d4` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025cfc` | `0x80025d0c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025ef0` | `0x80026108` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026108` | `0x800262fc` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026690` | `0x80026d14` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027c30` | `0x8002814c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800281ac` | `0x8002824c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028e98` | `0x8002968c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029d20` | `0x80029fbc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029fbc` | `0x80029ff4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002bc50` | `0x8002c148` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c148` | `0x8002cd6c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cd6c` | `0x8002d33c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d33c` | `0x8002ecfc` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002ecfc` | `0x8002ed20` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002ed20` | `0x8002ed3c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002ed3c` | `0x8002f000` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f000` | `0x8002f010` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f010` | `0x8002f044` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f044` | `0x8002f05c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f05c` | `0x8002f06c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f06c` | `0x8002f0a0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f0a0` | `0x8002f0a8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f0a8` | `0x8002f154` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f154` | `0x8002f160` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f160` | `0x8002f188` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f188` | `0x8002f1c8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f1c8` | `0x8002f1f8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f1f8` | `0x8002f1f8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f1f8` | `0x8002f210` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f210` | `0x8002f218` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f218` | `0x8002f224` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f224` | `0x8002f23c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f23c` | `0x8002f254` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f254` | `0x8002f268` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f268` | `0x8002f288` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f288` | `0x8002f29c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f29c` | `0x8002f2c8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f2c8` | `0x8002f310` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f310` | `0x8002f3f0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f3f0` | `0x8002f4a0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f4a0` | `0x8002f4c0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f4c0` | `0x8002f534` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f534` | `0x8002f544` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f544` | `0x8002f550` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f550` | `0x8002f634` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f634` | `0x8002f65c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f65c` | `0x8002f670` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f670` | `0x8002f670` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f670` | `0x8002f670` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f670` | `0x8002f690` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f690` | `0x8002f6c0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f6c0` | `0x8002f6e4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f6e4` | `0x8002f704` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f704` | `0x8002f708` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f708` | `0x8002f794` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f794` | `0x8002f7a4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f7a4` | `0x8002f7b4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f7b4` | `0x8002f8e4` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f8e4` | `0x8002f8e4` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f8e4` | `0x8002fa80` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002fa80` | `0x8002fa80` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002fa80` | `0x8002fae0` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030898` | `0x800308c0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800308c0` | `0x80030ad0` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030bd0` | `0x80030c7c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030c7c` | `0x80030d00` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030d00` | `0x80030d80` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030d80` | `0x80030e38` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030e38` | `0x80030eac` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030eac` | `0x80031070` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031070` | `0x800310e0` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800310e0` | `0x80031158` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031158` | `0x80031308` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031308` | `0x80031384` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031384` | `0x800313d4` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800313d4` | `0x80031424` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031424` | `0x80031454` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031454` | `0x80031498` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031498` | `0x800314dc` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800314dc` | `0x8003158c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8003158c` | `0x800316e8` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800316e8` | `0x800319e4` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800319e4` | `0x80031bc0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031bc0` | `0x80031c6c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031c6c` | `0x80031de4` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031de4` | `0x80031fb0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031fb0` | `0x800320e4` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800321d4` | `0x800322b0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800322b0` | `0x80032400` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032400` | `0x800325dc` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x8003278c` | `0x80032978` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032978` | `0x800329cc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800329cc` | `0x80032a14` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032a14` | `0x80032ae8` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032ae8` | `0x80032bc8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032bc8` | `0x80032d80` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033798` | `0x80033814` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033814` | `0x80033900` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033f64` | `0x80033fd4` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033fd4` | `0x80034034` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034410` | `0x80034464` | 84 | `bnq_sub` | UNCONVERTED |
| `0x8003462c` | `0x80034898` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034898` | `0x80034bd8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034bd8` | `0x80034e88` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034e88` | `0x800351bc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800351bc` | `0x80035544` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035544` | `0x80035664` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035684` | `0x80035ab4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035ab4` | `0x80035ef8` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035f4c` | `0x800360f8` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x8003656c` | `0x80036730` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036ec0` | `0x80037198` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037a84` | `0x80037b14` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037b14` | `0x80037be4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037dbc` | `0x80037e18` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038008` | `0x80038274` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038274` | `0x80038594` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038594` | `0x80038844` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038844` | `0x80038a20` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038a20` | `0x80038d68` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038eb4` | `0x8003a718` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a718` | `0x8003b954` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003ba78` | `0x8003bb94` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003bba4` | `0x8003bbd4` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003bbd4` | `0x8003c170` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c170` | `0x8003c480` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c480` | `0x8003c488` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c488` | `0x8003c48c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c48c` | `0x8003c670` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c768` | `0x8003c9b0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c9b0` | `0x8003d014` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d014` | `0x8003d130` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d130` | `0x8003d348` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d348` | `0x8003d388` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d388` | `0x8003d3d0` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d3d0` | `0x8003d420` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d420` | `0x8003d478` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d478` | `0x8003d4d8` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d4d8` | `0x8003d540` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d540` | `0x8003d5b0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d5b0` | `0x8003d628` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d628` | `0x8003d6a8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d6a8` | `0x8003d730` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d730` | `0x8003d7c0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d7c0` | `0x8003d858` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d858` | `0x8003d8f8` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d8f8` | `0x8003d9a0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d9a0` | `0x8003da50` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003da50` | `0x8003db08` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003db08` | `0x8003dbc8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003dbc8` | `0x8003dc90` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003dc90` | `0x8003dd60` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003dd60` | `0x8003de38` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003de38` | `0x8003df18` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003df18` | `0x8003e000` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e000` | `0x8003e0f0` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e0f0` | `0x8003e1e8` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e1e8` | `0x8003e2e8` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e2e8` | `0x8003e3f0` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e3f0` | `0x8003e500` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e500` | `0x8003e618` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e618` | `0x8003e738` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e738` | `0x8003e860` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e860` | `0x8003e990` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e990` | `0x8003eac8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003eac8` | `0x8003ec08` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003ec08` | `0x8003ec80` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ec80` | `0x8003ecf8` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003ecf8` | `0x8003ed70` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003ed70` | `0x8003ede8` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ede8` | `0x8003ee60` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ee60` | `0x8003eed8` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003eed8` | `0x8003ef50` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ef50` | `0x8003efc8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003efc8` | `0x8003f040` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f040` | `0x8003f0b8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f0b8` | `0x8003f130` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f130` | `0x8003f1a8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f1a8` | `0x8003f220` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f220` | `0x8003f298` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f298` | `0x8003f310` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f310` | `0x8003f388` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f388` | `0x8003f3f8` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f3f8` | `0x8003f468` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f468` | `0x8003f4d8` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f4d8` | `0x8003f548` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f548` | `0x8003f5b8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f5b8` | `0x8003f628` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f628` | `0x8003f698` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f698` | `0x8003f708` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f708` | `0x8003f778` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f778` | `0x8003f7e8` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f7e8` | `0x8003f858` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f858` | `0x8003f8c8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f8c8` | `0x8003f938` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f938` | `0x8003f9a8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f9a8` | `0x8003fa18` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fa18` | `0x8003fa88` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003fa88` | `0x8003faa0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003faa0` | `0x8003fab4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003fab4` | `0x8003fb40` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003fb40` | `0x8003fb58` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003fb58` | `0x8003fb6c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003fb6c` | `0x8003fbf4` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003fbf4` | `0x8003fc0c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003fc0c` | `0x8003fc20` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003fc20` | `0x8003fc40` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003fc40` | `0x8003fc48` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003fc48` | `0x8003fc54` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003fc54` | `0x8003fc58` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003fc58` | `0x8003fcdc` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fcdc` | `0x8003fd84` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fd84` | `0x8003feb8` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003feb8` | `0x8003ff60` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003ff60` | `0x80040058` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040058` | `0x800400f0` | 152 | `h_LT` | UNCONVERTED |
| `0x800400f0` | `0x80040188` | 152 | `h_GT` | UNCONVERTED |
| `0x80040188` | `0x8004021c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004021c` | `0x800402b0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800402b0` | `0x80040334` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040334` | `0x80040394` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040394` | `0x80040408` | 116 | `h_AND` | UNCONVERTED |
| `0x80040408` | `0x8004047c` | 116 | `h_OR` | UNCONVERTED |
| `0x8004047c` | `0x800404f0` | 116 | `h_XOR` | UNCONVERTED |
| `0x800404f0` | `0x80040550` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040550` | `0x8004063c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x8004063c` | `0x800407dc` | 416 | `h_SHL` | UNCONVERTED |
| `0x800407dc` | `0x8004097c` | 416 | `h_SHR` | UNCONVERTED |
| `0x8004097c` | `0x80040b30` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040b30` | `0x80040c30` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040c30` | `0x80040c64` | 52 | `h_POP` | UNCONVERTED |
| `0x80040c64` | `0x80040fb0` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80040fb0` | `0x80041290` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041290` | `0x800413b0` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800413b0` | `0x800413f4` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800413f4` | `0x80041438` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041438` | `0x80041488` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041488` | `0x800414d8` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800414d8` | `0x80041528` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041528` | `0x80041578` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041578` | `0x800415c8` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800415c8` | `0x80041618` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041618` | `0x80041668` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041668` | `0x800416b8` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800416b8` | `0x80041708` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041708` | `0x80041758` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041758` | `0x800417a8` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800417a8` | `0x800417f8` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800417f8` | `0x80041848` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041848` | `0x80041898` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041898` | `0x800418e8` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800418e8` | `0x80041980` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041980` | `0x80041a6c` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041a6c` | `0x80041ab0` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041ab0` | `0x80041ccc` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041ccc` | `0x80041e9c` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041e9c` | `0x80041ee0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041ee0` | `0x800420ac` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800420ac` | `0x800420b4` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800420b4` | `0x80042174` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042174` | `0x80042268` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042268` | `0x800422ac` | 68 | `h_PC` | UNCONVERTED |
| `0x800422ac` | `0x80042534` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042534` | `0x80042828` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042828` | `0x80042b3c` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042b3c` | `0x80042e70` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042e70` | `0x800431c4` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800431c4` | `0x80043538` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043538` | `0x800437e0` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800437e0` | `0x80043ae8` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043ae8` | `0x80044154` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044154` | `0x800446fc` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800446fc` | `0x80044c7c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044c7c` | `0x80045508` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045508` | `0x800455f4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800455f4` | `0x800456c4` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800456c4` | `0x80045944` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80045944` | `0x800462dc` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800462dc` | `0x800468c0` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800468c0` | `0x800468dc` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800468dc` | `0x80047e00` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047e00` | `0x80047e4c` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047e4c` | `0x80047ff0` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047ff0` | `0x80048db8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048db8` | `0x8004b064` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b064` | `0x8004c1dc` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c1dc` | `0x8004ce40` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004ce40` | `0x8004dc48` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004dc48` | `0x8004e8ac` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e8ac` | `0x8004f164` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f164` | `0x8004fa58` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004fa58` | `0x8004fff4` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fff4` | `0x800506a0` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x800506a0` | `0x800506c0` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800506c0` | `0x80050d6c` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050d6c` | `0x80050d8c` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050d8c` | `0x800516bc` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800516bc` | `0x80051a08` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051a08` | `0x80051b78` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051b78` | `0x80051b7c` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051b7c` | `0x80051c04` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051c04` | `0x80051df8` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051df8` | `0x80051e28` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051e28` | `0x80051e3c` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051e3c` | `0x80051e4c` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051e4c` | `0x80051e7c` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051e7c` | `0x80052070` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052070` | `0x800520a0` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800520a0` | `0x800520b4` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800520b4` | `0x800520c4` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800520c4` | `0x800520f4` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800520f4` | `0x80052118` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052118` | `0x80052148` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052148` | `0x8005233c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x8005233c` | `0x8005236c` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x8005236c` | `0x80052380` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052380` | `0x80052390` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052390` | `0x800523c0` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800523c0` | `0x800525b4` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800525b4` | `0x800525e4` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800525e4` | `0x800525f8` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800525f8` | `0x80052608` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052608` | `0x80052638` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052638` | `0x8005282c` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x8005282c` | `0x8005285c` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x8005285c` | `0x80052870` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052870` | `0x80052880` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052880` | `0x800528b0` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800528b0` | `0x800528b0` | 0 | `.exit_label` | UNCONVERTED |
| `0x800528b0` | `0x800528cc` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052a58` | `0x80052c8c` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x8005318c` | `0x800532bc` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800532bc` | `0x80053318` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053318` | `0x80053338` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053338` | `0x80053474` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053644` | `0x80053650` | 12 | `requests_hash_verify` | TAIL |
