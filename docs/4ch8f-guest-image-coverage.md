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
not linked** (42 of 384 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053a60), 342624 bytes (`RegionMap.textSizeBytes = 0x53a60`)

- symbols in `.text`: 905 (342 converted, 563 unconverted)
- covered by converted `_prog`s: 84444 bytes (24.65%)
- NOT covered: 258180 bytes (75.35%), 564 ranges

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
| `0x80003b14` | `0x80003d80` | 620 | `witness_lookup_by_hash` | UNCONVERTED |
| `0x80003d80` | `0x80003d9c` | 28 | `widx_record_ptr` | UNCONVERTED |
| `0x80003d9c` | `0x80003ddc` | 64 | `widx_cmp32` | UNCONVERTED |
| `0x80003ddc` | `0x80003e0c` | 48 | `widx_swap_records` | UNCONVERTED |
| `0x80003e0c` | `0x80003f08` | 252 | `widx_sift_down` | UNCONVERTED |
| `0x80003f08` | `0x80004180` | 632 | `witness_index_build` | UNCONVERTED |
| `0x80004180` | `0x80004248` | 200 | `witness_lookup_by_hash_indexed` | UNCONVERTED |
| `0x80004248` | `0x800044b4` | 620 | `witness_codes_lookup_by_hash` | UNCONVERTED |
| `0x800044b4` | `0x800044d0` | 28 | `wcidx_record_ptr` | UNCONVERTED |
| `0x800044d0` | `0x80004510` | 64 | `wcidx_cmp32` | UNCONVERTED |
| `0x80004510` | `0x80004540` | 48 | `wcidx_swap_records` | UNCONVERTED |
| `0x80004540` | `0x8000463c` | 252 | `wcidx_sift_down` | UNCONVERTED |
| `0x8000463c` | `0x800048b4` | 632 | `witness_codes_index_build` | UNCONVERTED |
| `0x800048b4` | `0x8000497c` | 200 | `witness_codes_lookup_by_hash_indexed` | UNCONVERTED |
| `0x80004fe0` | `0x8000506c` | 140 | `rlp_item_size` | UNCONVERTED |
| `0x8000506c` | `0x80005140` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80005140` | `0x80005214` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80005514` | `0x8000555c` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x8000555c` | `0x800055c4` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800055c4` | `0x8000561c` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x8000561c` | `0x80005684` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005684` | `0x80005878` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x80009b38` | `0x80009cfc` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009cfc` | `0x80009d68` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a428` | `0x8000a624` | 508 | `mpt_indexed_stream_leaf_hash` | UNCONVERTED |
| `0x8000a624` | `0x8000a824` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a824` | `0x8000a964` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a964` | `0x8000ac20` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000ac20` | `0x8000ad10` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ad10` | `0x8000ae80` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000bdbc` | `0x8000c34c` | 1424 | `block_header_ssz_to_rlp` | UNCONVERTED |
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
| `0x800139b0` | `0x80013b80` | 464 | `chain_config_valid` | UNCONVERTED |
| `0x80013b80` | `0x80013cec` | 364 | `public_keys_valid` | UNCONVERTED |
| `0x80013cec` | `0x80013d00` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d00` | `0x80013d0c` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013d0c` | `0x80013d5c` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013d5c` | `0x80013d7c` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013d7c` | `0x80013de0` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013de0` | `0x80014088` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014088` | `0x800142dc` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x800142dc` | `0x80014490` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80014490` | `0x800148a0` | 1040 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80015090` | `0x80015288` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155a8` | `0x800157d8` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x800158d4` | `0x80015bc8` | 756 | `simple_transfer_intrinsic_gas` | UNCONVERTED |
| `0x80015bc8` | `0x800186c4` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800186c4` | `0x80019410` | 3404 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019410` | `0x8001962c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019914` | `0x800199a8` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a1a0` | `0x8001a3f8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a3f8` | `0x8001a670` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a670` | `0x8001a904` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001ab40` | `0x8001ace0` | 416 | `bal_gas_valid_from_builder` | UNCONVERTED |
| `0x8001aef4` | `0x8001b1ac` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b574` | `0x8001b7ec` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b7ec` | `0x8001ba90` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001ba90` | `0x8001c56c` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c874` | `0x8001c8bc` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c9f0` | `0x8001cebc` | 1228 | `stage_runtime_payload_code` | UNCONVERTED |
| `0x8001cebc` | `0x8001cf4c` | 144 | `stage_runtime_payload_witness_context` | UNCONVERTED |
| `0x8001cf4c` | `0x8001d134` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d134` | `0x8001d190` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d190` | `0x8001d25c` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d25c` | `0x8001d330` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d330` | `0x8001e258` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001eb2c` | `0x8001ec40` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ec40` | `0x8001ef48` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f6e0` | `0x8001f834` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8001fbfc` | `0x8001fc3c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fc3c` | `0x8001fe9c` | 608 | `bal_storage_change_values` | UNCONVERTED |
| `0x8001fe9c` | `0x8001ffe4` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001ffe4` | `0x80020014` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020014` | `0x800201a4` | 400 | `storage_read_record` | UNCONVERTED |
| `0x800201a4` | `0x80020320` | 380 | `storage_read_record_block` | UNCONVERTED |
| `0x80020320` | `0x80020564` | 580 | `storage_write_record` | UNCONVERTED |
| `0x80020564` | `0x800206f4` | 400 | `destroy_storage` | UNCONVERTED |
| `0x800206f4` | `0x80020898` | 420 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x80020898` | `0x80020958` | 192 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x80020958` | `0x80020980` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x80020980` | `0x80020a7c` | 252 | `storage_writes_undo_push` | UNCONVERTED |
| `0x80020a7c` | `0x80020bc0` | 324 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80020bc0` | `0x80020e00` | 576 | `account_write_record` | UNCONVERTED |
| `0x80020e00` | `0x80020f40` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x80020f40` | `0x80021008` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x80021008` | `0x800210b8` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x800210b8` | `0x80021168` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80021168` | `0x800212d8` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x800212d8` | `0x800213e4` | 268 | `account_writes_auth_block` | UNCONVERTED |
| `0x800213e4` | `0x80021488` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x80021488` | `0x80021614` | 396 | `account_writes_lookup_current` | UNCONVERTED |
| `0x80021614` | `0x800218e8` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x800218e8` | `0x80021a04` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021a04` | `0x80021bc8` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021bc8` | `0x80021e58` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021e58` | `0x80021ea8` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x80021ea8` | `0x80021f9c` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x80021f9c` | `0x800224a0` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x800224a0` | `0x8002252c` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x8002252c` | `0x8002264c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x8002264c` | `0x80022750` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x80022750` | `0x8002290c` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x8002290c` | `0x80022d68` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x80022d68` | `0x80023010` | 680 | `bal_map_final_value_matches` | UNCONVERTED |
| `0x80023010` | `0x80023100` | 240 | `bal_map_builder_consistent` | UNCONVERTED |
| `0x8002334c` | `0x80023368` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023368` | `0x800233dc` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800233dc` | `0x8002342c` | 80 | `keccak_final` | UNCONVERTED |
| `0x8002342c` | `0x80023458` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023458` | `0x80023538` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023538` | `0x800235b8` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x800235b8` | `0x800235e8` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800235e8` | `0x80023728` | 320 | `bal_rlp_emit_bytes` | UNCONVERTED |
| `0x80023728` | `0x800237ec` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800237ec` | `0x80023840` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023840` | `0x80023870` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023870` | `0x800238b0` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800238b0` | `0x800238e8` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800238e8` | `0x80023928` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023928` | `0x800239e4` | 188 | `bal_serializer_slot_written` | UNCONVERTED |
| `0x800239e4` | `0x80023a88` | 164 | `bal_serializer_slot_seen_before` | UNCONVERTED |
| `0x80023a88` | `0x80023aa0` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80023aa0` | `0x80023b7c` | 220 | `bal_serializer_measure_reads` | UNCONVERTED |
| `0x80023b7c` | `0x80023bac` | 48 | `bal_serializer_slot_to_le` | UNCONVERTED |
| `0x80023bac` | `0x80023bdc` | 48 | `bal_serializer_balance_to_le` | UNCONVERTED |
| `0x80023bdc` | `0x80023ce8` | 268 | `bal_serializer_measure_slot` | UNCONVERTED |
| `0x80023ce8` | `0x80023dc8` | 224 | `bal_serializer_measure_storage` | UNCONVERTED |
| `0x80023dc8` | `0x80023ea4` | 220 | `bal_serializer_measure_balance` | UNCONVERTED |
| `0x80023ea4` | `0x80023f8c` | 232 | `bal_serializer_measure_nonce` | UNCONVERTED |
| `0x80023f8c` | `0x8002407c` | 240 | `bal_serializer_measure_code` | UNCONVERTED |
| `0x8002407c` | `0x80024160` | 228 | `bal_serializer_measure_account` | UNCONVERTED |
| `0x80024160` | `0x80024340` | 480 | `bal_serializer_emit_storage` | UNCONVERTED |
| `0x80024340` | `0x8002440c` | 204 | `bal_serializer_emit_reads` | UNCONVERTED |
| `0x8002440c` | `0x80024550` | 324 | `bal_serializer_emit_balance` | UNCONVERTED |
| `0x80024550` | `0x800246c8` | 376 | `bal_serializer_emit_nonce` | UNCONVERTED |
| `0x800246c8` | `0x800247fc` | 308 | `bal_serializer_emit_code` | UNCONVERTED |
| `0x800247fc` | `0x80024928` | 300 | `bal_serializer_emit_account` | UNCONVERTED |
| `0x80024928` | `0x800249b8` | 144 | `bal_serializer_measure_outer` | UNCONVERTED |
| `0x800249b8` | `0x80024a60` | 168 | `bal_serializer_emit_outer` | UNCONVERTED |
| `0x80024a60` | `0x80024c5c` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024c5c` | `0x80024cf4` | 152 | `bal_serializer_verify` | UNCONVERTED |
| `0x80024cf4` | `0x80024e00` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024e00` | `0x80024e64` | 100 | `bal_builder_incorporate_touched_accounts` | UNCONVERTED |
| `0x80024e64` | `0x8002502c` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x8002502c` | `0x80025314` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025314` | `0x800253fc` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800253fc` | `0x800254d8` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x800254d8` | `0x800255b0` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800255b0` | `0x800256d4` | 292 | `account_read_record` | UNCONVERTED |
| `0x800256d4` | `0x80025728` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x80025728` | `0x80025888` | 352 | `code_read_record` | UNCONVERTED |
| `0x80025888` | `0x80025934` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x80025934` | `0x80025a58` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025a58` | `0x80025b50` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025b50` | `0x80025b78` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x80025b78` | `0x80025cf4` | 380 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80026148` | `0x80026378` | 560 | `multi_tx_nth_context` | UNCONVERTED |
| `0x80026378` | `0x80026388` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x8002656c` | `0x80026784` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026784` | `0x80026978` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026d0c` | `0x80027390` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028110` | `0x80028248` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80028248` | `0x800282ac` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x800282ac` | `0x800287c8` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028828` | `0x800288c8` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028f80` | `0x80029110` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x80029110` | `0x8002948c` | 892 | `eip7702_authority_asof` | UNCONVERTED |
| `0x8002948c` | `0x80029c80` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029c80` | `0x80029fb8` | 824 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x80029fb8` | `0x8002a0a8` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x8002a314` | `0x8002a5b0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a5b0` | `0x8002a5e8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002aa10` | `0x8002aafc` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002c240` | `0x8002c730` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c730` | `0x8002d17c` | 2636 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d17c` | `0x8002d74c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d74c` | `0x8002f10c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f10c` | `0x8002f130` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f130` | `0x8002f14c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f14c` | `0x8002f410` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f410` | `0x8002f420` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f420` | `0x8002f454` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f454` | `0x8002f46c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f46c` | `0x8002f47c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f47c` | `0x8002f4b0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f4b0` | `0x8002f4b8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f4b8` | `0x8002f564` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f564` | `0x8002f570` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f570` | `0x8002f598` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f598` | `0x8002f5d8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f5d8` | `0x8002f608` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f608` | `0x8002f608` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f608` | `0x8002f620` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f620` | `0x8002f628` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f628` | `0x8002f634` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f634` | `0x8002f64c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f64c` | `0x8002f664` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f664` | `0x8002f678` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f678` | `0x8002f698` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f698` | `0x8002f6ac` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f6ac` | `0x8002f6d8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f6d8` | `0x8002f720` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f720` | `0x8002f800` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f800` | `0x8002f8b0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f8b0` | `0x8002f8d0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f8d0` | `0x8002f944` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f944` | `0x8002f954` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f954` | `0x8002f960` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f960` | `0x8002fa44` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fa44` | `0x8002fa6c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fa6c` | `0x8002fa80` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fa80` | `0x8002fa80` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fa80` | `0x8002fa80` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fa80` | `0x8002faa0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002faa0` | `0x8002fad0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fad0` | `0x8002faf4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002faf4` | `0x8002fb14` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fb14` | `0x8002fb18` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fb18` | `0x8002fba4` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fba4` | `0x8002fbb4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fbb4` | `0x8002fbc4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fbc4` | `0x8002fcf4` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fcf4` | `0x8002fcf4` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fcf4` | `0x8002fe90` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002fe90` | `0x8002fef0` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8002fef0` | `0x80030048` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x80030ca8` | `0x80030cd0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030cd0` | `0x80030ee0` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030f40` | `0x80030fe0` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x80030fe0` | `0x8003108c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x8003108c` | `0x80031110` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031110` | `0x80031190` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031190` | `0x80031248` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031248` | `0x800312bc` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800312bc` | `0x80031480` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031480` | `0x800314f0` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800314f0` | `0x80031568` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031568` | `0x80031718` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031718` | `0x80031794` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031794` | `0x800317e4` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800317e4` | `0x80031834` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031834` | `0x80031864` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031864` | `0x800318a8` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800318a8` | `0x800318ec` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800318ec` | `0x8003199c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8003199c` | `0x80031af8` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031af8` | `0x80031df4` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031df4` | `0x80031fd0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031fd0` | `0x8003207c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x8003207c` | `0x800321f4` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800321f4` | `0x800323c0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800323c0` | `0x800324f4` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800325e4` | `0x800326c0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800326c0` | `0x80032810` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032810` | `0x800329ec` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032b9c` | `0x80032d88` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032d88` | `0x80032ddc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032ddc` | `0x80032e24` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032e24` | `0x80032ef8` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032ef8` | `0x80032fd8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032fd8` | `0x80033190` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033190` | `0x800332ac` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x8003392c` | `0x80033a08` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x80033a08` | `0x80033b78` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80033ba8` | `0x80033c24` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033c24` | `0x80033d10` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034374` | `0x800343e4` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800343e4` | `0x80034444` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034690` | `0x80034820` | 400 | `bnq_mul` | UNCONVERTED |
| `0x80034820` | `0x80034874` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034a3c` | `0x80034ca8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034ca8` | `0x80034fe8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034fe8` | `0x80035298` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035298` | `0x800355cc` | 820 | `bng2_double` | UNCONVERTED |
| `0x800355cc` | `0x80035954` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035954` | `0x80035a74` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035a94` | `0x80035ec4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035ec4` | `0x80036308` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003635c` | `0x80036508` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036628` | `0x800367f0` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x8003697c` | `0x80036b40` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800372d0` | `0x800375a8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003797c` | `0x80037a8c` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80037a8c` | `0x80037be0` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80037be0` | `0x80037d18` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037e94` | `0x80037f24` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037f24` | `0x80037ff4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037ff4` | `0x800381cc` | 472 | `blq_mul` | UNCONVERTED |
| `0x800381cc` | `0x80038228` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038418` | `0x80038684` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038684` | `0x800389a4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x800389a4` | `0x80038c54` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038c54` | `0x80038e30` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038e30` | `0x80039178` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800392c4` | `0x8003ab28` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ab28` | `0x8003bd64` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003bde4` | `0x8003be88` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003be88` | `0x8003bfa4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003bfb4` | `0x8003bfe4` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003bfe4` | `0x8003c580` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c580` | `0x8003c890` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c890` | `0x8003c898` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c898` | `0x8003c89c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c89c` | `0x8003ca80` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cb10` | `0x8003cb78` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003cb78` | `0x8003cdc0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cdc0` | `0x8003d424` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d424` | `0x8003d540` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d540` | `0x8003d758` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d758` | `0x8003d798` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d798` | `0x8003d7e0` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d7e0` | `0x8003d830` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d830` | `0x8003d888` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d888` | `0x8003d8e8` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d8e8` | `0x8003d950` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d950` | `0x8003d9c0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d9c0` | `0x8003da38` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003da38` | `0x8003dab8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dab8` | `0x8003db40` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003db40` | `0x8003dbd0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dbd0` | `0x8003dc68` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003dc68` | `0x8003dd08` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dd08` | `0x8003ddb0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003ddb0` | `0x8003de60` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003de60` | `0x8003df18` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003df18` | `0x8003dfd8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003dfd8` | `0x8003e0a0` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e0a0` | `0x8003e170` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e170` | `0x8003e248` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e248` | `0x8003e328` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e328` | `0x8003e410` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e410` | `0x8003e500` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e500` | `0x8003e5f8` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e5f8` | `0x8003e6f8` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e6f8` | `0x8003e800` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e800` | `0x8003e910` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e910` | `0x8003ea28` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ea28` | `0x8003eb48` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003eb48` | `0x8003ec70` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ec70` | `0x8003eda0` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003eda0` | `0x8003eed8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003eed8` | `0x8003f018` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f018` | `0x8003f090` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f090` | `0x8003f108` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f108` | `0x8003f180` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f180` | `0x8003f1f8` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f1f8` | `0x8003f270` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f270` | `0x8003f2e8` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f2e8` | `0x8003f360` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f360` | `0x8003f3d8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f3d8` | `0x8003f450` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f450` | `0x8003f4c8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f4c8` | `0x8003f540` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f540` | `0x8003f5b8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f5b8` | `0x8003f630` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f630` | `0x8003f6a8` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f6a8` | `0x8003f720` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f720` | `0x8003f798` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f798` | `0x8003f808` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f808` | `0x8003f878` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f878` | `0x8003f8e8` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f8e8` | `0x8003f958` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f958` | `0x8003f9c8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f9c8` | `0x8003fa38` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fa38` | `0x8003faa8` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003faa8` | `0x8003fb18` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fb18` | `0x8003fb88` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fb88` | `0x8003fbf8` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fbf8` | `0x8003fc68` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fc68` | `0x8003fcd8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fcd8` | `0x8003fd48` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003fd48` | `0x8003fdb8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003fdb8` | `0x8003fe28` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fe28` | `0x8003fe98` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003fe98` | `0x8003feb0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003feb0` | `0x8003fec4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003fec4` | `0x8003ff50` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003ff50` | `0x8003ff68` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003ff68` | `0x8003ff7c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003ff7c` | `0x80040004` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040004` | `0x8004001c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8004001c` | `0x80040030` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040030` | `0x80040050` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040050` | `0x80040058` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040058` | `0x80040064` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040064` | `0x80040068` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040068` | `0x800400ec` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800400ec` | `0x80040194` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040194` | `0x800402c8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800402c8` | `0x80040370` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040370` | `0x80040468` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040468` | `0x80040500` | 152 | `h_LT` | UNCONVERTED |
| `0x80040500` | `0x80040598` | 152 | `h_GT` | UNCONVERTED |
| `0x80040598` | `0x8004062c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004062c` | `0x800406c0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800406c0` | `0x80040744` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040744` | `0x800407a4` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800407a4` | `0x80040818` | 116 | `h_AND` | UNCONVERTED |
| `0x80040818` | `0x8004088c` | 116 | `h_OR` | UNCONVERTED |
| `0x8004088c` | `0x80040900` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040900` | `0x80040960` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040960` | `0x80040a4c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040a4c` | `0x80040bec` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040bec` | `0x80040d8c` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040d8c` | `0x80040f40` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040f40` | `0x80041040` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041040` | `0x80041074` | 52 | `h_POP` | UNCONVERTED |
| `0x80041074` | `0x800413f0` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800413f0` | `0x80041700` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80041700` | `0x80041838` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041838` | `0x8004187c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004187c` | `0x800418c0` | 68 | `h_GAS` | UNCONVERTED |
| `0x800418c0` | `0x80041910` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041910` | `0x80041960` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041960` | `0x800419b0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800419b0` | `0x80041a00` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041a00` | `0x80041a50` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041a50` | `0x80041aa0` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041aa0` | `0x80041af0` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041af0` | `0x80041b40` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041b40` | `0x80041b90` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041b90` | `0x80041be0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041be0` | `0x80041c30` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041c30` | `0x80041c80` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041c80` | `0x80041cd0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041cd0` | `0x80041d20` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041d20` | `0x80041d70` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041d70` | `0x80041e08` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041e08` | `0x80041ef4` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041ef4` | `0x80041f38` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041f38` | `0x80042154` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042154` | `0x8004233c` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x8004233c` | `0x80042380` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042380` | `0x80042564` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042564` | `0x8004256c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x8004256c` | `0x8004262c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004262c` | `0x80042720` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042720` | `0x80042764` | 68 | `h_PC` | UNCONVERTED |
| `0x80042764` | `0x800429ec` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800429ec` | `0x80042ce0` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042ce0` | `0x80042ff4` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042ff4` | `0x80043328` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043328` | `0x8004367c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x8004367c` | `0x800439f0` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800439f0` | `0x80043c98` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043c98` | `0x80043fa0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043fa0` | `0x8004460c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004460c` | `0x80044bcc` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044bcc` | `0x8004514c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x8004514c` | `0x800459d8` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800459d8` | `0x80045ac4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045ac4` | `0x80045b94` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045b94` | `0x80045e2c` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80045e2c` | `0x800467bc` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x800467bc` | `0x80046d98` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046d98` | `0x80046db4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046db4` | `0x800482d8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800482d8` | `0x80048324` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048324` | `0x800484e0` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800484e0` | `0x800492a8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800492a8` | `0x8004b4e4` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b4e4` | `0x8004c5ec` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c5ec` | `0x8004d24c` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d24c` | `0x8004e054` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e054` | `0x8004ecb4` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ecb4` | `0x8004f56c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f56c` | `0x8004fe60` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004fe60` | `0x800503fc` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800503fc` | `0x80050aa8` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050aa8` | `0x80050ac8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050ac8` | `0x80051174` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051174` | `0x80051194` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051194` | `0x80051ac4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051ac4` | `0x80051e10` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051e10` | `0x80051f80` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051f80` | `0x80051f84` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051f84` | `0x8005200c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005200c` | `0x80052200` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052200` | `0x80052230` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052230` | `0x80052244` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052244` | `0x80052254` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052254` | `0x80052284` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052284` | `0x80052478` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052478` | `0x800524a8` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800524a8` | `0x800524bc` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800524bc` | `0x800524cc` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800524cc` | `0x800524fc` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800524fc` | `0x80052520` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052520` | `0x80052550` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052550` | `0x80052744` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052744` | `0x80052774` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052774` | `0x80052788` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052788` | `0x80052798` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052798` | `0x800527c8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800527c8` | `0x800529bc` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800529bc` | `0x800529ec` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800529ec` | `0x80052a00` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052a00` | `0x80052a10` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052a10` | `0x80052a40` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052a40` | `0x80052c34` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052c34` | `0x80052c64` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052c64` | `0x80052c78` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c78` | `0x80052c88` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052c88` | `0x80052cb8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052cb8` | `0x80052cb8` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052cb8` | `0x80052cd4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052d0c` | `0x80052d28` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x80052d28` | `0x80052d44` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x80052d44` | `0x80052e60` | 284 | `stage_system_call` | UNCONVERTED |
| `0x80052e60` | `0x80053094` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053094` | `0x8005349c` | 1032 | `process_block_start_system_transactions` | UNCONVERTED |
| `0x8005349c` | `0x8005359c` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x8005359c` | `0x800536cc` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800536cc` | `0x80053728` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053728` | `0x80053748` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053748` | `0x80053884` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053a54` | `0x80053a60` | 12 | `requests_hash_verify` | TAIL |
