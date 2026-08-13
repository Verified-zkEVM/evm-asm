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

`.text` = [0x80000000, 0x80053f38), 343864 bytes (`RegionMap.textSizeBytes = 0x53f38`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121600 bytes (35.36%)
- NOT covered: 222264 bytes (64.64%), 458 ranges

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
| `0x80009b54` | `0x80009d18` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009d18` | `0x80009d84` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a640` | `0x8000a840` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a840` | `0x8000a980` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a980` | `0x8000ac3c` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000ac3c` | `0x8000ad2c` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ad2c` | `0x8000ae9c` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e154` | `0x8000f470` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f8a0` | `0x8000fa80` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fa80` | `0x8000fb64` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fb64` | `0x8000fc40` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fc40` | `0x8000fcd4` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fcd4` | `0x8000fd90` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fd90` | `0x8000fe40` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000fe40` | `0x8000ff24` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000ff24` | `0x8000ff60` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000ff60` | `0x80010090` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x80010090` | `0x800101b4` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800101b4` | `0x80010264` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010264` | `0x800103e0` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800103e0` | `0x800104b8` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800104b8` | `0x80010648` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010648` | `0x800107e4` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800107e4` | `0x80010894` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010894` | `0x800108fc` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x800108fc` | `0x80010998` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010998` | `0x80010fcc` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010fcc` | `0x800112b4` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800112b4` | `0x8001160c` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x8001160c` | `0x80011ae8` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011ae8` | `0x80011d8c` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011d8c` | `0x80011ea8` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011ea8` | `0x80012160` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x80012160` | `0x80012380` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012380` | `0x80012718` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012718` | `0x8001282c` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x8001282c` | `0x8001284c` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x8001284c` | `0x80012ad4` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012ad4` | `0x80012bb8` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012bb8` | `0x80012c60` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012c60` | `0x80013394` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013394` | `0x800139cc` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013d08` | `0x80013d1c` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013d1c` | `0x80013d28` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013d28` | `0x80013d78` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013d78` | `0x80013d98` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013d98` | `0x80013dfc` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013dfc` | `0x800140a4` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800140a4` | `0x800142f8` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x800142f8` | `0x800144ac` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800150ac` | `0x800152a4` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800155c4` | `0x800157f4` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015be4` | `0x800186e0` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800186e0` | `0x80019474` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019474` | `0x80019690` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019978` | `0x80019a0c` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a204` | `0x8001a45c` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a45c` | `0x8001a6d4` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a6d4` | `0x8001a968` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001af64` | `0x8001b280` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b648` | `0x8001b8c0` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b8c0` | `0x8001bb64` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb64` | `0x8001c628` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c93c` | `0x8001c984` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d014` | `0x8001d1fc` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1fc` | `0x8001d258` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d258` | `0x8001d324` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d324` | `0x8001d3f8` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3f8` | `0x8001e378` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ec4c` | `0x8001ed60` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ed60` | `0x8001f068` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fd1c` | `0x8001fd5c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ffbc` | `0x80020104` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020104` | `0x80020134` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020684` | `0x80020814` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021a08` | `0x80021b24` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021b24` | `0x80021ce8` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021ce8` | `0x80021f78` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x8002264c` | `0x8002276c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x8002346c` | `0x80023488` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023488` | `0x800234fc` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800234fc` | `0x8002354c` | 80 | `keccak_final` | UNCONVERTED |
| `0x8002354c` | `0x80023578` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023578` | `0x80023658` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023658` | `0x800236d8` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x800236d8` | `0x80023708` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023848` | `0x8002390c` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x8002390c` | `0x80023960` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023960` | `0x80023990` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023990` | `0x800239d0` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800239d0` | `0x80023a08` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023a08` | `0x80023a48` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023ba8` | `0x80023bc0` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024b80` | `0x80024d7c` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024e14` | `0x80024f20` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024f84` | `0x8002514c` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x8002514c` | `0x80025434` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025434` | `0x8002551c` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x8002551c` | `0x800255f8` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x800255f8` | `0x800256d0` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025a84` | `0x80025ba8` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025ba8` | `0x80025ca0` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800264c8` | `0x800264d8` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x800266bc` | `0x800268d4` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x800268d4` | `0x80026ac8` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026e5c` | `0x800274e0` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800283fc` | `0x80028918` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028978` | `0x80028a18` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029664` | `0x80029e58` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a4ec` | `0x8002a788` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a788` | `0x8002a7c0` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c418` | `0x8002c910` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c910` | `0x8002d534` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d534` | `0x8002db04` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002db04` | `0x8002f4c4` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f4c4` | `0x8002f4e8` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f4e8` | `0x8002f504` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f504` | `0x8002f7c8` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f7c8` | `0x8002f7d8` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f7d8` | `0x8002f80c` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f80c` | `0x8002f824` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f824` | `0x8002f834` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f834` | `0x8002f868` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f868` | `0x8002f870` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f870` | `0x8002f91c` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f91c` | `0x8002f928` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f928` | `0x8002f950` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f950` | `0x8002f990` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f990` | `0x8002f9c0` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f9c0` | `0x8002f9c0` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f9c0` | `0x8002f9d8` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f9d8` | `0x8002f9e0` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f9e0` | `0x8002f9ec` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f9ec` | `0x8002fa04` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fa04` | `0x8002fa1c` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fa1c` | `0x8002fa30` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002fa30` | `0x8002fa50` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002fa50` | `0x8002fa64` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002fa64` | `0x8002fa90` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fa90` | `0x8002fad8` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fad8` | `0x8002fbb8` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fbb8` | `0x8002fc68` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fc68` | `0x8002fc88` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fc88` | `0x8002fcfc` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fcfc` | `0x8002fd0c` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fd0c` | `0x8002fd18` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fd18` | `0x8002fdfc` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fdfc` | `0x8002fe24` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fe24` | `0x8002fe38` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe38` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe38` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe58` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fe58` | `0x8002fe88` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fe88` | `0x8002feac` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002feac` | `0x8002fecc` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fecc` | `0x8002fed0` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fed0` | `0x8002ff5c` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002ff5c` | `0x8002ff6c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002ff6c` | `0x8002ff7c` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002ff7c` | `0x800300ac` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800300ac` | `0x800300ac` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800300ac` | `0x80030248` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030248` | `0x80030248` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030248` | `0x800302a8` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031060` | `0x80031088` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031088` | `0x80031298` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031398` | `0x80031444` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031444` | `0x800314c8` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800314c8` | `0x80031548` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031548` | `0x80031600` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031600` | `0x80031674` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031674` | `0x80031838` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031838` | `0x800318a8` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800318a8` | `0x80031920` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031920` | `0x80031ad0` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031ad0` | `0x80031b4c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031b4c` | `0x80031b9c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031b9c` | `0x80031bec` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031bec` | `0x80031c1c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031c1c` | `0x80031c60` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031c60` | `0x80031ca4` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031ca4` | `0x80031d54` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031d54` | `0x80031eb0` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031eb0` | `0x800321ac` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800321ac` | `0x80032388` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032388` | `0x80032434` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032434` | `0x800325ac` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800325ac` | `0x80032778` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032778` | `0x800328ac` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x8003299c` | `0x80032a78` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032a78` | `0x80032bc8` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032bc8` | `0x80032da4` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032f54` | `0x80033140` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80033140` | `0x80033194` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033194` | `0x800331dc` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800331dc` | `0x800332b0` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800332b0` | `0x80033390` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033390` | `0x80033548` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033f60` | `0x80033fdc` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033fdc` | `0x800340c8` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x8003472c` | `0x8003479c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x8003479c` | `0x800347fc` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034bd8` | `0x80034c2c` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034df4` | `0x80035060` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035060` | `0x800353a0` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800353a0` | `0x80035650` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035650` | `0x80035984` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035984` | `0x80035d0c` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035d0c` | `0x80035e2c` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035e4c` | `0x8003627c` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x8003627c` | `0x800366c0` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036714` | `0x800368c0` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036d34` | `0x80036ef8` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037688` | `0x80037960` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003824c` | `0x800382dc` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800382dc` | `0x800383ac` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038584` | `0x800385e0` | 92 | `blq_sub` | UNCONVERTED |
| `0x800387d0` | `0x80038a3c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038a3c` | `0x80038d5c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038d5c` | `0x8003900c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003900c` | `0x800391e8` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800391e8` | `0x80039530` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x8003967c` | `0x8003aee0` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003aee0` | `0x8003c11c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c240` | `0x8003c35c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c36c` | `0x8003c39c` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c39c` | `0x8003c938` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c938` | `0x8003cc48` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cc48` | `0x8003cc50` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cc50` | `0x8003cc54` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cc54` | `0x8003ce38` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cf30` | `0x8003d178` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d178` | `0x8003d7dc` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d7dc` | `0x8003d8f8` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d8f8` | `0x8003db10` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003db10` | `0x8003db50` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003db50` | `0x8003db98` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003db98` | `0x8003dbe8` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003dbe8` | `0x8003dc40` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dc40` | `0x8003dca0` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dca0` | `0x8003dd08` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dd08` | `0x8003dd78` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dd78` | `0x8003ddf0` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003ddf0` | `0x8003de70` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003de70` | `0x8003def8` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003def8` | `0x8003df88` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003df88` | `0x8003e020` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e020` | `0x8003e0c0` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e0c0` | `0x8003e168` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e168` | `0x8003e218` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e218` | `0x8003e2d0` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e2d0` | `0x8003e390` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e390` | `0x8003e458` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e458` | `0x8003e528` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e528` | `0x8003e600` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e600` | `0x8003e6e0` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e6e0` | `0x8003e7c8` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e7c8` | `0x8003e8b8` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e8b8` | `0x8003e9b0` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e9b0` | `0x8003eab0` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003eab0` | `0x8003ebb8` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003ebb8` | `0x8003ecc8` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ecc8` | `0x8003ede0` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ede0` | `0x8003ef00` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ef00` | `0x8003f028` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f028` | `0x8003f158` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f158` | `0x8003f290` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f290` | `0x8003f3d0` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f3d0` | `0x8003f448` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f448` | `0x8003f4c0` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f4c0` | `0x8003f538` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f538` | `0x8003f5b0` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f5b0` | `0x8003f628` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f628` | `0x8003f6a0` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f6a0` | `0x8003f718` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f718` | `0x8003f790` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f790` | `0x8003f808` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f808` | `0x8003f880` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f880` | `0x8003f8f8` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f8f8` | `0x8003f970` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f970` | `0x8003f9e8` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f9e8` | `0x8003fa60` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003fa60` | `0x8003fad8` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fad8` | `0x8003fb50` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fb50` | `0x8003fbc0` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fbc0` | `0x8003fc30` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fc30` | `0x8003fca0` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fca0` | `0x8003fd10` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fd10` | `0x8003fd80` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fd80` | `0x8003fdf0` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fdf0` | `0x8003fe60` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fe60` | `0x8003fed0` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fed0` | `0x8003ff40` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003ff40` | `0x8003ffb0` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003ffb0` | `0x80040020` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x80040020` | `0x80040090` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040090` | `0x80040100` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040100` | `0x80040170` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040170` | `0x800401e0` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800401e0` | `0x80040250` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040250` | `0x80040268` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040268` | `0x8004027c` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8004027c` | `0x80040308` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040308` | `0x80040320` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040320` | `0x80040334` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040334` | `0x800403bc` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800403bc` | `0x800403d4` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800403d4` | `0x800403e8` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800403e8` | `0x80040408` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040408` | `0x80040410` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040410` | `0x8004041c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8004041c` | `0x80040420` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040420` | `0x800404a4` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800404a4` | `0x8004054c` | 168 | `h_ADD` | UNCONVERTED |
| `0x8004054c` | `0x80040680` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040680` | `0x80040728` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040728` | `0x80040820` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040820` | `0x800408b8` | 152 | `h_LT` | UNCONVERTED |
| `0x800408b8` | `0x80040950` | 152 | `h_GT` | UNCONVERTED |
| `0x80040950` | `0x800409e4` | 148 | `h_SLT` | UNCONVERTED |
| `0x800409e4` | `0x80040a78` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040a78` | `0x80040afc` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040afc` | `0x80040b5c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040b5c` | `0x80040bd0` | 116 | `h_AND` | UNCONVERTED |
| `0x80040bd0` | `0x80040c44` | 116 | `h_OR` | UNCONVERTED |
| `0x80040c44` | `0x80040cb8` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040cb8` | `0x80040d18` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040d18` | `0x80040e04` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040e04` | `0x80040fa4` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040fa4` | `0x80041144` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041144` | `0x800412f8` | 436 | `h_SAR` | UNCONVERTED |
| `0x800412f8` | `0x800413f8` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800413f8` | `0x8004142c` | 52 | `h_POP` | UNCONVERTED |
| `0x8004142c` | `0x800417a8` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800417a8` | `0x80041ab8` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80041ab8` | `0x80041bf0` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041bf0` | `0x80041c34` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041c34` | `0x80041c78` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041c78` | `0x80041cc8` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041cc8` | `0x80041d18` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041d18` | `0x80041d68` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041d68` | `0x80041db8` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041db8` | `0x80041e08` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041e08` | `0x80041e58` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041e58` | `0x80041ea8` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041ea8` | `0x80041ef8` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041ef8` | `0x80041f48` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041f48` | `0x80041f98` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041f98` | `0x80041fe8` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041fe8` | `0x80042038` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042038` | `0x80042088` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042088` | `0x800420d8` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800420d8` | `0x80042128` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042128` | `0x800421c0` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800421c0` | `0x800422ac` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800422ac` | `0x800422f0` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800422f0` | `0x8004250c` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x8004250c` | `0x800426f4` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x800426f4` | `0x80042738` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042738` | `0x8004291c` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x8004291c` | `0x80042924` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042924` | `0x800429e4` | 192 | `h_JUMP` | UNCONVERTED |
| `0x800429e4` | `0x80042ad8` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042ad8` | `0x80042b1c` | 68 | `h_PC` | UNCONVERTED |
| `0x80042b1c` | `0x80042da4` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042da4` | `0x80043098` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80043098` | `0x800433ac` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800433ac` | `0x800436e0` | 820 | `h_LOG2` | UNCONVERTED |
| `0x800436e0` | `0x80043a34` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043a34` | `0x80043da8` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043da8` | `0x80044050` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044050` | `0x80044358` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044358` | `0x800449c4` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x800449c4` | `0x80044f84` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044f84` | `0x80045504` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045504` | `0x80045d90` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045d90` | `0x80045e7c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045e7c` | `0x80045f4c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045f4c` | `0x800461e4` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x800461e4` | `0x80046b74` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046b74` | `0x80047150` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80047150` | `0x8004716c` | 28 | `h_INVALID` | UNCONVERTED |
| `0x8004716c` | `0x80048690` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048690` | `0x800486dc` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x800486dc` | `0x80048898` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048898` | `0x80049660` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049660` | `0x8004b91c` | 8892 | `h_CALL` | UNCONVERTED |
| `0x8004b91c` | `0x8004caa4` | 4488 | `h_CALLCODE` | UNCONVERTED |
| `0x8004caa4` | `0x8004d718` | 3188 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d718` | `0x8004e520` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e520` | `0x8004f194` | 3188 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f194` | `0x8004fa4c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fa4c` | `0x80050340` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050340` | `0x800508dc` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800508dc` | `0x80050f88` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050f88` | `0x80050fa8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050fa8` | `0x80051654` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051654` | `0x80051674` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051674` | `0x80051fa4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051fa4` | `0x800522f0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800522f0` | `0x80052460` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052460` | `0x80052464` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052464` | `0x800524ec` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800524ec` | `0x800526e0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800526e0` | `0x80052710` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052710` | `0x80052724` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052724` | `0x80052734` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052734` | `0x80052764` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052764` | `0x80052958` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052958` | `0x80052988` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052988` | `0x8005299c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x8005299c` | `0x800529ac` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800529ac` | `0x800529dc` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800529dc` | `0x80052a00` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052a00` | `0x80052a30` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052a30` | `0x80052c24` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052c24` | `0x80052c54` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052c54` | `0x80052c68` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c68` | `0x80052c78` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052c78` | `0x80052ca8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052ca8` | `0x80052e9c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052e9c` | `0x80052ecc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052ecc` | `0x80052ee0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052ee0` | `0x80052ef0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052ef0` | `0x80052f20` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052f20` | `0x80053114` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053114` | `0x80053144` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053144` | `0x80053158` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053158` | `0x80053168` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053168` | `0x80053198` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053198` | `0x80053198` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053198` | `0x800531b4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053340` | `0x80053574` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053a74` | `0x80053ba4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053ba4` | `0x80053c00` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053c00` | `0x80053c20` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053c20` | `0x80053d5c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053f2c` | `0x80053f38` | 12 | `requests_hash_verify` | TAIL |
