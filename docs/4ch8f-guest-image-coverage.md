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
not linked** (50 of 424 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053964), 342372 bytes (`RegionMap.textSizeBytes = 0x53964`)

- symbols in `.text`: 905 (374 converted, 531 unconverted)
- covered by converted `_prog`s: 95608 bytes (27.93%)
- NOT covered: 246764 bytes (72.07%), 532 ranges

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
| `0x80014490` | `0x800148a0` | 1040 | `log_records_encode_rlp` | UNCONVERTED |
| `0x80015090` | `0x80015288` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155a8` | `0x800157d8` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
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
| `0x8001ce48` | `0x8001d030` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d030` | `0x8001d08c` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d08c` | `0x8001d158` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d158` | `0x8001d22c` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d22c` | `0x8001e154` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ea28` | `0x8001eb3c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001eb3c` | `0x8001ee44` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f5dc` | `0x8001f730` | 340 | `secp256k1_point_add` | UNCONVERTED |
| `0x8001faf8` | `0x8001fb38` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fd98` | `0x8001fee0` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001fee0` | `0x8001ff10` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001ff10` | `0x800200a0` | 400 | `storage_read_record` | UNCONVERTED |
| `0x800200a0` | `0x8002021c` | 380 | `storage_read_record_block` | UNCONVERTED |
| `0x8002021c` | `0x80020460` | 580 | `storage_write_record` | UNCONVERTED |
| `0x80020460` | `0x800205f0` | 400 | `destroy_storage` | UNCONVERTED |
| `0x800205f0` | `0x80020794` | 420 | `storage_writes_block_upsert` | UNCONVERTED |
| `0x80020794` | `0x80020854` | 192 | `write_sets_incorporate_tx` | UNCONVERTED |
| `0x80020854` | `0x8002087c` | 40 | `write_sets_discard_tx` | UNCONVERTED |
| `0x8002087c` | `0x80020978` | 252 | `storage_writes_undo_push` | UNCONVERTED |
| `0x80020978` | `0x80020abc` | 324 | `write_sets_restore_frame` | UNCONVERTED |
| `0x80020abc` | `0x80020cfc` | 576 | `account_write_record` | UNCONVERTED |
| `0x80020cfc` | `0x80020e3c` | 320 | `account_writes_latest_balance` | UNCONVERTED |
| `0x80020e3c` | `0x80020f04` | 200 | `account_writes_latest_balance_block` | UNCONVERTED |
| `0x80020f04` | `0x80020fb4` | 176 | `account_writes_latest_nonce_block` | UNCONVERTED |
| `0x80020fb4` | `0x80021064` | 176 | `account_writes_latest_nonce_tx` | UNCONVERTED |
| `0x80021064` | `0x800211d4` | 368 | `account_writes_auth_current` | UNCONVERTED |
| `0x800211d4` | `0x800212e0` | 268 | `account_writes_auth_block` | UNCONVERTED |
| `0x800212e0` | `0x80021384` | 164 | `account_writes_created_contains` | UNCONVERTED |
| `0x80021384` | `0x80021510` | 396 | `account_writes_lookup_current` | UNCONVERTED |
| `0x80021510` | `0x800217e4` | 724 | `account_writes_tombstone_balance_zero` | UNCONVERTED |
| `0x800217e4` | `0x80021900` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021900` | `0x80021ac4` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021ac4` | `0x80021d54` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021d54` | `0x80021da4` | 80 | `account_writes_commit_pending` | UNCONVERTED |
| `0x80021da4` | `0x80021e98` | 244 | `account_writes_is_absent` | UNCONVERTED |
| `0x80021e98` | `0x8002239c` | 1284 | `account_writes_emit_builder_tx` | UNCONVERTED |
| `0x8002239c` | `0x80022428` | 140 | `account_writes_incorporate_tx` | UNCONVERTED |
| `0x80022428` | `0x80022548` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022548` | `0x8002264c` | 260 | `account_writes_restore_frame` | UNCONVERTED |
| `0x8002264c` | `0x80022808` | 444 | `account_resolve_pre_state` | UNCONVERTED |
| `0x80022808` | `0x80022c64` | 1116 | `account_resolve_execution_state` | UNCONVERTED |
| `0x80023248` | `0x80023264` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023264` | `0x800232d8` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800232d8` | `0x80023328` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023328` | `0x80023354` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023354` | `0x80023434` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023434` | `0x800234b4` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x800234b4` | `0x800234e4` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023624` | `0x800236e8` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800236e8` | `0x8002373c` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x8002373c` | `0x8002376c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x8002376c` | `0x800237ac` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800237ac` | `0x800237e4` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800237e4` | `0x80023824` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023984` | `0x8002399c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x8002495c` | `0x80024b58` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024bf0` | `0x80024cfc` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024d60` | `0x80024f28` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024f28` | `0x80025210` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025210` | `0x800252f8` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800252f8` | `0x800253d4` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x800253d4` | `0x800254ac` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800254ac` | `0x800255d0` | 292 | `account_read_record` | UNCONVERTED |
| `0x800255d0` | `0x80025624` | 84 | `account_at_header_state_root_tracked` | UNCONVERTED |
| `0x80025624` | `0x80025784` | 352 | `code_read_record` | UNCONVERTED |
| `0x80025784` | `0x80025830` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x80025830` | `0x80025954` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025954` | `0x80025a4c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025a4c` | `0x80025a74` | 40 | `read_sets_discard_tx` | UNCONVERTED |
| `0x80025a74` | `0x80025bf0` | 380 | `stage_blockhash_m29` | UNCONVERTED |
| `0x80026274` | `0x80026284` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026468` | `0x80026680` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026680` | `0x80026874` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026c08` | `0x8002728c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x8002800c` | `0x80028144` | 312 | `multi_tx_running_sender_balance_step` | UNCONVERTED |
| `0x80028144` | `0x800281a8` | 100 | `sender_debit_from_gas` | UNCONVERTED |
| `0x800281a8` | `0x800286c4` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028724` | `0x800287c4` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028e7c` | `0x8002900c` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x8002900c` | `0x80029388` | 892 | `eip7702_authority_asof` | UNCONVERTED |
| `0x80029388` | `0x80029b7c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029b7c` | `0x80029eb4` | 824 | `block_verdict_tx_state_gas_inline_prepare` | UNCONVERTED |
| `0x80029eb4` | `0x80029fa4` | 240 | `block_verdict_tx_state_gas_inline_finalize` | UNCONVERTED |
| `0x8002a210` | `0x8002a4ac` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a4ac` | `0x8002a4e4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002a90c` | `0x8002a9f8` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002c13c` | `0x8002c62c` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c62c` | `0x8002d088` | 2652 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d088` | `0x8002d658` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d658` | `0x8002f018` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f018` | `0x8002f03c` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f03c` | `0x8002f058` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f058` | `0x8002f31c` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f31c` | `0x8002f32c` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f32c` | `0x8002f360` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f360` | `0x8002f378` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f378` | `0x8002f388` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f388` | `0x8002f3bc` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f3bc` | `0x8002f3c4` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f3c4` | `0x8002f470` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f470` | `0x8002f47c` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f47c` | `0x8002f4a4` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f4a4` | `0x8002f4e4` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f4e4` | `0x8002f514` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f514` | `0x8002f514` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f514` | `0x8002f52c` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f52c` | `0x8002f534` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f534` | `0x8002f540` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f540` | `0x8002f558` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f558` | `0x8002f570` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f570` | `0x8002f584` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f584` | `0x8002f5a4` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f5a4` | `0x8002f5b8` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f5b8` | `0x8002f5e4` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f5e4` | `0x8002f62c` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f62c` | `0x8002f70c` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f70c` | `0x8002f7bc` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f7bc` | `0x8002f7dc` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f7dc` | `0x8002f850` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f850` | `0x8002f860` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f860` | `0x8002f86c` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f86c` | `0x8002f950` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f950` | `0x8002f978` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f978` | `0x8002f98c` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f98c` | `0x8002f98c` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f98c` | `0x8002f98c` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f98c` | `0x8002f9ac` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f9ac` | `0x8002f9dc` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f9dc` | `0x8002fa00` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fa00` | `0x8002fa20` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fa20` | `0x8002fa24` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fa24` | `0x8002fab0` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fab0` | `0x8002fac0` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fac0` | `0x8002fad0` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fad0` | `0x8002fc00` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fc00` | `0x8002fc00` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fc00` | `0x8002fd9c` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002fd9c` | `0x8002fdfc` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8002fdfc` | `0x8002ff54` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x80030bb4` | `0x80030bdc` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030bdc` | `0x80030dec` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030e4c` | `0x80030eec` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x80030eec` | `0x80030f98` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030f98` | `0x8003101c` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x8003101c` | `0x8003109c` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x8003109c` | `0x80031154` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031154` | `0x800311c8` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800311c8` | `0x8003138c` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x8003138c` | `0x800313fc` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800313fc` | `0x80031474` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031474` | `0x80031624` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031624` | `0x800316a0` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x800316a0` | `0x800316f0` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800316f0` | `0x80031740` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031740` | `0x80031770` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031770` | `0x800317b4` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800317b4` | `0x800317f8` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800317f8` | `0x800318a8` | 176 | `modexp_mul` | UNCONVERTED |
| `0x800318a8` | `0x80031a04` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031a04` | `0x80031d00` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031d00` | `0x80031edc` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031edc` | `0x80031f88` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031f88` | `0x80032100` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032100` | `0x800322cc` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800322cc` | `0x80032400` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800324f0` | `0x800325cc` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800325cc` | `0x8003271c` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x8003271c` | `0x800328f8` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032aa8` | `0x80032c94` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032c94` | `0x80032ce8` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032ce8` | `0x80032d30` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032d30` | `0x80032e04` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032e04` | `0x80032ee4` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032ee4` | `0x8003309c` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x8003309c` | `0x800331b8` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x80033838` | `0x80033914` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x80033914` | `0x80033a84` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80033ab4` | `0x80033b30` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033b30` | `0x80033c1c` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034280` | `0x800342f0` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800342f0` | `0x80034350` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x8003459c` | `0x8003472c` | 400 | `bnq_mul` | UNCONVERTED |
| `0x8003472c` | `0x80034780` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034948` | `0x80034bb4` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034bb4` | `0x80034ef4` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034ef4` | `0x800351a4` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800351a4` | `0x800354d8` | 820 | `bng2_double` | UNCONVERTED |
| `0x800354d8` | `0x80035860` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035860` | `0x80035980` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x800359a0` | `0x80035dd0` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035dd0` | `0x80036214` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036268` | `0x80036414` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036534` | `0x800366fc` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80036888` | `0x80036a4c` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800371dc` | `0x800374b4` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037888` | `0x80037998` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80037998` | `0x80037aec` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80037aec` | `0x80037c24` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037da0` | `0x80037e30` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037e30` | `0x80037f00` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037f00` | `0x800380d8` | 472 | `blq_mul` | UNCONVERTED |
| `0x800380d8` | `0x80038134` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038324` | `0x80038590` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038590` | `0x800388b0` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x800388b0` | `0x80038b60` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038b60` | `0x80038d3c` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038d3c` | `0x80039084` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800391d0` | `0x8003aa34` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003aa34` | `0x8003bc70` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003bcf0` | `0x8003bd94` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003bd94` | `0x8003beb0` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003bec0` | `0x8003bef0` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003bef0` | `0x8003c48c` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c48c` | `0x8003c79c` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c79c` | `0x8003c7a4` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c7a4` | `0x8003c7a8` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c7a8` | `0x8003c98c` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003ca1c` | `0x8003ca84` | 104 | `nonstorage_effect_latest_nonce` | UNCONVERTED |
| `0x8003ca84` | `0x8003cccc` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cccc` | `0x8003d330` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d330` | `0x8003d44c` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d44c` | `0x8003d664` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d664` | `0x8003d6a4` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d6a4` | `0x8003d6ec` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d6ec` | `0x8003d73c` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d73c` | `0x8003d794` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d794` | `0x8003d7f4` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d7f4` | `0x8003d85c` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d85c` | `0x8003d8cc` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d8cc` | `0x8003d944` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d944` | `0x8003d9c4` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d9c4` | `0x8003da4c` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003da4c` | `0x8003dadc` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dadc` | `0x8003db74` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003db74` | `0x8003dc14` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dc14` | `0x8003dcbc` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003dcbc` | `0x8003dd6c` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003dd6c` | `0x8003de24` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003de24` | `0x8003dee4` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003dee4` | `0x8003dfac` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003dfac` | `0x8003e07c` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e07c` | `0x8003e154` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e154` | `0x8003e234` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e234` | `0x8003e31c` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e31c` | `0x8003e40c` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e40c` | `0x8003e504` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e504` | `0x8003e604` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e604` | `0x8003e70c` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e70c` | `0x8003e81c` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e81c` | `0x8003e934` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e934` | `0x8003ea54` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ea54` | `0x8003eb7c` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003eb7c` | `0x8003ecac` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003ecac` | `0x8003ede4` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003ede4` | `0x8003ef24` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003ef24` | `0x8003ef9c` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ef9c` | `0x8003f014` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f014` | `0x8003f08c` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f08c` | `0x8003f104` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f104` | `0x8003f17c` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f17c` | `0x8003f1f4` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f1f4` | `0x8003f26c` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f26c` | `0x8003f2e4` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f2e4` | `0x8003f35c` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f35c` | `0x8003f3d4` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f3d4` | `0x8003f44c` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f44c` | `0x8003f4c4` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f4c4` | `0x8003f53c` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f53c` | `0x8003f5b4` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f5b4` | `0x8003f62c` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f62c` | `0x8003f6a4` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f6a4` | `0x8003f714` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f714` | `0x8003f784` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f784` | `0x8003f7f4` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f7f4` | `0x8003f864` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f864` | `0x8003f8d4` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f8d4` | `0x8003f944` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f944` | `0x8003f9b4` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f9b4` | `0x8003fa24` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fa24` | `0x8003fa94` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fa94` | `0x8003fb04` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fb04` | `0x8003fb74` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fb74` | `0x8003fbe4` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fbe4` | `0x8003fc54` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003fc54` | `0x8003fcc4` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003fcc4` | `0x8003fd34` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fd34` | `0x8003fda4` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003fda4` | `0x8003fdbc` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003fdbc` | `0x8003fdd0` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003fdd0` | `0x8003fe5c` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003fe5c` | `0x8003fe74` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003fe74` | `0x8003fe88` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003fe88` | `0x8003ff10` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003ff10` | `0x8003ff28` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003ff28` | `0x8003ff3c` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003ff3c` | `0x8003ff5c` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003ff5c` | `0x8003ff64` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003ff64` | `0x8003ff70` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003ff70` | `0x8003ff74` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003ff74` | `0x8003fff8` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fff8` | `0x800400a0` | 168 | `h_ADD` | UNCONVERTED |
| `0x800400a0` | `0x800401d4` | 308 | `h_MUL` | UNCONVERTED |
| `0x800401d4` | `0x8004027c` | 168 | `h_SUB` | UNCONVERTED |
| `0x8004027c` | `0x80040374` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040374` | `0x8004040c` | 152 | `h_LT` | UNCONVERTED |
| `0x8004040c` | `0x800404a4` | 152 | `h_GT` | UNCONVERTED |
| `0x800404a4` | `0x80040538` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040538` | `0x800405cc` | 148 | `h_SGT` | UNCONVERTED |
| `0x800405cc` | `0x80040650` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040650` | `0x800406b0` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800406b0` | `0x80040724` | 116 | `h_AND` | UNCONVERTED |
| `0x80040724` | `0x80040798` | 116 | `h_OR` | UNCONVERTED |
| `0x80040798` | `0x8004080c` | 116 | `h_XOR` | UNCONVERTED |
| `0x8004080c` | `0x8004086c` | 96 | `h_NOT` | UNCONVERTED |
| `0x8004086c` | `0x80040958` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040958` | `0x80040af8` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040af8` | `0x80040c98` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040c98` | `0x80040e4c` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040e4c` | `0x80040f4c` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040f4c` | `0x80040f80` | 52 | `h_POP` | UNCONVERTED |
| `0x80040f80` | `0x800412fc` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800412fc` | `0x8004160c` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x8004160c` | `0x80041744` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041744` | `0x80041788` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041788` | `0x800417cc` | 68 | `h_GAS` | UNCONVERTED |
| `0x800417cc` | `0x8004181c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x8004181c` | `0x8004186c` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x8004186c` | `0x800418bc` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800418bc` | `0x8004190c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8004190c` | `0x8004195c` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x8004195c` | `0x800419ac` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800419ac` | `0x800419fc` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x800419fc` | `0x80041a4c` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041a4c` | `0x80041a9c` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041a9c` | `0x80041aec` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041aec` | `0x80041b3c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041b3c` | `0x80041b8c` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041b8c` | `0x80041bdc` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041bdc` | `0x80041c2c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041c2c` | `0x80041c7c` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041c7c` | `0x80041d14` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041d14` | `0x80041e00` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041e00` | `0x80041e44` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041e44` | `0x80042060` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042060` | `0x80042248` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042248` | `0x8004228c` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x8004228c` | `0x80042470` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042470` | `0x80042478` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042478` | `0x80042538` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042538` | `0x8004262c` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x8004262c` | `0x80042670` | 68 | `h_PC` | UNCONVERTED |
| `0x80042670` | `0x800428f8` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800428f8` | `0x80042bec` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042bec` | `0x80042f00` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042f00` | `0x80043234` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043234` | `0x80043588` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043588` | `0x800438fc` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800438fc` | `0x80043ba4` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043ba4` | `0x80043eac` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043eac` | `0x80044518` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044518` | `0x80044ad8` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044ad8` | `0x80045058` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045058` | `0x800458e4` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800458e4` | `0x800459d0` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800459d0` | `0x80045aa0` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045aa0` | `0x80045d38` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80045d38` | `0x800466c8` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x800466c8` | `0x80046ca4` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046ca4` | `0x80046cc0` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046cc0` | `0x800481e4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800481e4` | `0x80048230` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048230` | `0x800483ec` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800483ec` | `0x800491b4` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800491b4` | `0x8004b3f0` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b3f0` | `0x8004c4f8` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c4f8` | `0x8004d158` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d158` | `0x8004df60` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004df60` | `0x8004ebc0` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ebc0` | `0x8004f478` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f478` | `0x8004fd6c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004fd6c` | `0x80050308` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050308` | `0x800509b4` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x800509b4` | `0x800509d4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800509d4` | `0x80051080` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051080` | `0x800510a0` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800510a0` | `0x800519d0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800519d0` | `0x80051d1c` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051d1c` | `0x80051e8c` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051e8c` | `0x80051e90` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051e90` | `0x80051f18` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051f18` | `0x8005210c` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x8005210c` | `0x8005213c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005213c` | `0x80052150` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052150` | `0x80052160` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052160` | `0x80052190` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052190` | `0x80052384` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052384` | `0x800523b4` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800523b4` | `0x800523c8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800523c8` | `0x800523d8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800523d8` | `0x80052408` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052408` | `0x8005242c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x8005242c` | `0x8005245c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x8005245c` | `0x80052650` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052650` | `0x80052680` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052680` | `0x80052694` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052694` | `0x800526a4` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x800526a4` | `0x800526d4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800526d4` | `0x800528c8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800528c8` | `0x800528f8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800528f8` | `0x8005290c` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x8005290c` | `0x8005291c` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x8005291c` | `0x8005294c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005294c` | `0x80052b40` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052b40` | `0x80052b70` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052b70` | `0x80052b84` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052b84` | `0x80052b94` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052b94` | `0x80052bc4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052bc4` | `0x80052bc4` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052bc4` | `0x80052be0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052c18` | `0x80052c34` | 28 | `derive_builder_deposit_requests` | UNCONVERTED |
| `0x80052c34` | `0x80052c50` | 28 | `derive_builder_exit_requests` | UNCONVERTED |
| `0x80052c50` | `0x80052d6c` | 284 | `stage_system_call` | UNCONVERTED |
| `0x80052d6c` | `0x80052fa0` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80052fa0` | `0x800533a0` | 1024 | `process_block_start_system_transactions` | UNCONVERTED |
| `0x800533a0` | `0x800534a0` | 256 | `parse_deposit_requests` | UNCONVERTED |
| `0x800534a0` | `0x800535d0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800535d0` | `0x8005362c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x8005362c` | `0x8005364c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005364c` | `0x80053788` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053958` | `0x80053964` | 12 | `requests_hash_verify` | TAIL |
