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
not linked** (72 of 504 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053b78), 342904 bytes (`RegionMap.textSizeBytes = 0x53b78`)

- symbols in `.text`: 906 (432 converted, 474 unconverted)
- covered by converted `_prog`s: 115836 bytes (33.78%)
- NOT covered: 227068 bytes (66.22%), 475 ranges

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
| `0x80015bc8` | `0x800186c4` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800186c4` | `0x80019410` | 3404 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019410` | `0x8001962c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019914` | `0x800199a8` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a1a0` | `0x8001a3f8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a3f8` | `0x8001a670` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a670` | `0x8001a904` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001aef4` | `0x8001b1ac` | 696 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b574` | `0x8001b7ec` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b7ec` | `0x8001ba90` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001ba90` | `0x8001c56c` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c874` | `0x8001c8bc` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001cf4c` | `0x8001d134` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d134` | `0x8001d190` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d190` | `0x8001d25c` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d25c` | `0x8001d330` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d330` | `0x8001e258` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001eb2c` | `0x8001ec40` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ec40` | `0x8001ef48` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fbfc` | `0x8001fc3c` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001fe9c` | `0x8001ffe4` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001ffe4` | `0x80020014` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020564` | `0x800206f4` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80020bc0` | `0x80020e00` | 576 | `account_write_record` | UNCONVERTED |
| `0x800218e8` | `0x80021a04` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021a04` | `0x80021bc8` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021bc8` | `0x80021e58` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x8002252c` | `0x8002264c` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x8002334c` | `0x80023368` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023368` | `0x800233dc` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x800233dc` | `0x8002342c` | 80 | `keccak_final` | UNCONVERTED |
| `0x8002342c` | `0x80023458` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023458` | `0x80023538` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023538` | `0x800235b8` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x800235b8` | `0x800235e8` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023728` | `0x800237ec` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x800237ec` | `0x80023840` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023840` | `0x80023870` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023870` | `0x800238b0` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x800238b0` | `0x800238e8` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800238e8` | `0x80023928` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023a88` | `0x80023aa0` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024a60` | `0x80024c5c` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024cf4` | `0x80024e00` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024e64` | `0x8002502c` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x8002502c` | `0x80025314` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025314` | `0x800253fc` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x800253fc` | `0x800254d8` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x800254d8` | `0x800255b0` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025728` | `0x80025888` | 352 | `code_read_record` | UNCONVERTED |
| `0x80025888` | `0x80025934` | 172 | `code_read_fetch` | UNCONVERTED |
| `0x80025934` | `0x80025a58` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025a58` | `0x80025b50` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026378` | `0x80026388` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x8002656c` | `0x80026784` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026784` | `0x80026978` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026d0c` | `0x80027390` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x800282ac` | `0x800287c8` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028828` | `0x800288c8` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028f80` | `0x80029110` | 400 | `eip7702_warm_recovered_authorities` | UNCONVERTED |
| `0x8002948c` | `0x80029c80` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a314` | `0x8002a5b0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a5b0` | `0x8002a5e8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002aa10` | `0x8002aafc` | 236 | `dispatcher_capture_exec_state_gas_differential` | UNCONVERTED |
| `0x8002c240` | `0x8002c730` | 1264 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c730` | `0x8002d29c` | 2924 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d29c` | `0x8002d86c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d86c` | `0x8002f22c` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f22c` | `0x8002f250` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f250` | `0x8002f26c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f26c` | `0x8002f530` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f530` | `0x8002f540` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f540` | `0x8002f574` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f574` | `0x8002f58c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f58c` | `0x8002f59c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f59c` | `0x8002f5d0` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f5d0` | `0x8002f5d8` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f5d8` | `0x8002f684` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f684` | `0x8002f690` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f690` | `0x8002f6b8` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f6b8` | `0x8002f6f8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f6f8` | `0x8002f728` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f728` | `0x8002f728` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f728` | `0x8002f740` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f740` | `0x8002f748` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f748` | `0x8002f754` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f754` | `0x8002f76c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f76c` | `0x8002f784` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f784` | `0x8002f798` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f798` | `0x8002f7b8` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f7b8` | `0x8002f7cc` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f7cc` | `0x8002f7f8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f7f8` | `0x8002f840` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f840` | `0x8002f920` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f920` | `0x8002f9d0` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f9d0` | `0x8002f9f0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f9f0` | `0x8002fa64` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fa64` | `0x8002fa74` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fa74` | `0x8002fa80` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fa80` | `0x8002fb64` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fb64` | `0x8002fb8c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fb8c` | `0x8002fba0` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fba0` | `0x8002fba0` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fba0` | `0x8002fba0` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fba0` | `0x8002fbc0` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fbc0` | `0x8002fbf0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fbf0` | `0x8002fc14` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fc14` | `0x8002fc34` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fc34` | `0x8002fc38` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fc38` | `0x8002fcc4` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fcc4` | `0x8002fcd4` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fcd4` | `0x8002fce4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fce4` | `0x8002fe14` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002fe14` | `0x8002fe14` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002fe14` | `0x8002ffb0` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002ffb0` | `0x8002ffb0` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002ffb0` | `0x80030010` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030010` | `0x80030168` | 344 | `balance_live_else_header_state_root` | UNCONVERTED |
| `0x80030dc8` | `0x80030df0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030df0` | `0x80031000` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031060` | `0x80031100` | 160 | `find_code_effect_by_hash` | UNCONVERTED |
| `0x80031100` | `0x800311ac` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x800311ac` | `0x80031230` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031230` | `0x800312b0` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x800312b0` | `0x80031368` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031368` | `0x800313dc` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800313dc` | `0x800315a0` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x800315a0` | `0x80031610` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031610` | `0x80031688` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031688` | `0x80031838` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031838` | `0x800318b4` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x800318b4` | `0x80031904` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031904` | `0x80031954` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031954` | `0x80031984` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031984` | `0x800319c8` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800319c8` | `0x80031a0c` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031a0c` | `0x80031abc` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031abc` | `0x80031c18` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031c18` | `0x80031f14` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x80031f14` | `0x800320f0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800320f0` | `0x8003219c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x8003219c` | `0x80032314` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032314` | `0x800324e0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800324e0` | `0x80032614` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032704` | `0x800327e0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800327e0` | `0x80032930` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032930` | `0x80032b0c` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032cbc` | `0x80032ea8` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032ea8` | `0x80032efc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032efc` | `0x80032f44` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032f44` | `0x80033018` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033018` | `0x800330f8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800330f8` | `0x800332b0` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x800332b0` | `0x800333cc` | 284 | `record_message_value_transfer` | UNCONVERTED |
| `0x80033a4c` | `0x80033b28` | 220 | `blsg_decode_g1` | UNCONVERTED |
| `0x80033b28` | `0x80033c98` | 368 | `blsg_scalar_mul` | UNCONVERTED |
| `0x80033cc8` | `0x80033d44` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033d44` | `0x80033e30` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034494` | `0x80034504` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034504` | `0x80034564` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800347b0` | `0x80034940` | 400 | `bnq_mul` | UNCONVERTED |
| `0x80034940` | `0x80034994` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034b5c` | `0x80034dc8` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034dc8` | `0x80035108` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035108` | `0x800353b8` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x800353b8` | `0x800356ec` | 820 | `bng2_double` | UNCONVERTED |
| `0x800356ec` | `0x80035a74` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035a74` | `0x80035b94` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035bb4` | `0x80035fe4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035fe4` | `0x80036428` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x8003647c` | `0x80036628` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036748` | `0x80036910` | 456 | `blsk_decompress_g1` | UNCONVERTED |
| `0x80036a9c` | `0x80036c60` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800373f0` | `0x800376c8` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037a9c` | `0x80037bac` | 272 | `blsg2_point_dbl` | UNCONVERTED |
| `0x80037bac` | `0x80037d00` | 340 | `blsg2_point_add` | UNCONVERTED |
| `0x80037d00` | `0x80037e38` | 312 | `blsg2_decode_g2` | UNCONVERTED |
| `0x80037fb4` | `0x80038044` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038044` | `0x80038114` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038114` | `0x800382ec` | 472 | `blq_mul` | UNCONVERTED |
| `0x800382ec` | `0x80038348` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038538` | `0x800387a4` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x800387a4` | `0x80038ac4` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038ac4` | `0x80038d74` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038d74` | `0x80038f50` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038f50` | `0x80039298` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800393e4` | `0x8003ac48` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ac48` | `0x8003be84` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003bf04` | `0x8003bfa8` | 164 | `call_frame_enter` | UNCONVERTED |
| `0x8003bfa8` | `0x8003c0c4` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c0d4` | `0x8003c104` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c104` | `0x8003c6a0` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c6a0` | `0x8003c9b0` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c9b0` | `0x8003c9b8` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c9b8` | `0x8003c9bc` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c9bc` | `0x8003cba0` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003cc98` | `0x8003cee0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003cee0` | `0x8003d544` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d544` | `0x8003d660` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d660` | `0x8003d878` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d878` | `0x8003d8b8` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d8b8` | `0x8003d900` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d900` | `0x8003d950` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d950` | `0x8003d9a8` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d9a8` | `0x8003da08` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003da08` | `0x8003da70` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003da70` | `0x8003dae0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dae0` | `0x8003db58` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003db58` | `0x8003dbd8` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dbd8` | `0x8003dc60` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003dc60` | `0x8003dcf0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003dcf0` | `0x8003dd88` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003dd88` | `0x8003de28` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003de28` | `0x8003ded0` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003ded0` | `0x8003df80` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003df80` | `0x8003e038` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e038` | `0x8003e0f8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e0f8` | `0x8003e1c0` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e1c0` | `0x8003e290` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e290` | `0x8003e368` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e368` | `0x8003e448` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e448` | `0x8003e530` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e530` | `0x8003e620` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e620` | `0x8003e718` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e718` | `0x8003e818` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e818` | `0x8003e920` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e920` | `0x8003ea30` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ea30` | `0x8003eb48` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003eb48` | `0x8003ec68` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ec68` | `0x8003ed90` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ed90` | `0x8003eec0` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003eec0` | `0x8003eff8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003eff8` | `0x8003f138` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f138` | `0x8003f1b0` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f1b0` | `0x8003f228` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f228` | `0x8003f2a0` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f2a0` | `0x8003f318` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f318` | `0x8003f390` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f390` | `0x8003f408` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f408` | `0x8003f480` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f480` | `0x8003f4f8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f4f8` | `0x8003f570` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f570` | `0x8003f5e8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f5e8` | `0x8003f660` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f660` | `0x8003f6d8` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f6d8` | `0x8003f750` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f750` | `0x8003f7c8` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f7c8` | `0x8003f840` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f840` | `0x8003f8b8` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f8b8` | `0x8003f928` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f928` | `0x8003f998` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f998` | `0x8003fa08` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fa08` | `0x8003fa78` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fa78` | `0x8003fae8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fae8` | `0x8003fb58` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fb58` | `0x8003fbc8` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fbc8` | `0x8003fc38` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fc38` | `0x8003fca8` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fca8` | `0x8003fd18` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fd18` | `0x8003fd88` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003fd88` | `0x8003fdf8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003fdf8` | `0x8003fe68` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003fe68` | `0x8003fed8` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003fed8` | `0x8003ff48` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003ff48` | `0x8003ffb8` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003ffb8` | `0x8003ffd0` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003ffd0` | `0x8003ffe4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003ffe4` | `0x80040070` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040070` | `0x80040088` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040088` | `0x8004009c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8004009c` | `0x80040124` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x80040124` | `0x8004013c` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8004013c` | `0x80040150` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040150` | `0x80040170` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040170` | `0x80040178` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040178` | `0x80040184` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040184` | `0x80040188` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040188` | `0x8004020c` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8004020c` | `0x800402b4` | 168 | `h_ADD` | UNCONVERTED |
| `0x800402b4` | `0x800403e8` | 308 | `h_MUL` | UNCONVERTED |
| `0x800403e8` | `0x80040490` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040490` | `0x80040588` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040588` | `0x80040620` | 152 | `h_LT` | UNCONVERTED |
| `0x80040620` | `0x800406b8` | 152 | `h_GT` | UNCONVERTED |
| `0x800406b8` | `0x8004074c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004074c` | `0x800407e0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800407e0` | `0x80040864` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040864` | `0x800408c4` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800408c4` | `0x80040938` | 116 | `h_AND` | UNCONVERTED |
| `0x80040938` | `0x800409ac` | 116 | `h_OR` | UNCONVERTED |
| `0x800409ac` | `0x80040a20` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040a20` | `0x80040a80` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040a80` | `0x80040b6c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040b6c` | `0x80040d0c` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040d0c` | `0x80040eac` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040eac` | `0x80041060` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041060` | `0x80041160` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041160` | `0x80041194` | 52 | `h_POP` | UNCONVERTED |
| `0x80041194` | `0x80041510` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x80041510` | `0x80041820` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x80041820` | `0x80041958` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041958` | `0x8004199c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004199c` | `0x800419e0` | 68 | `h_GAS` | UNCONVERTED |
| `0x800419e0` | `0x80041a30` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041a30` | `0x80041a80` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041a80` | `0x80041ad0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041ad0` | `0x80041b20` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041b20` | `0x80041b70` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041b70` | `0x80041bc0` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041bc0` | `0x80041c10` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041c10` | `0x80041c60` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041c60` | `0x80041cb0` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041cb0` | `0x80041d00` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041d00` | `0x80041d50` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041d50` | `0x80041da0` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041da0` | `0x80041df0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041df0` | `0x80041e40` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041e40` | `0x80041e90` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041e90` | `0x80041f28` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041f28` | `0x80042014` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042014` | `0x80042058` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042058` | `0x80042274` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042274` | `0x8004245c` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x8004245c` | `0x800424a0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800424a0` | `0x80042684` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042684` | `0x8004268c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x8004268c` | `0x8004274c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004274c` | `0x80042840` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042840` | `0x80042884` | 68 | `h_PC` | UNCONVERTED |
| `0x80042884` | `0x80042b0c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042b0c` | `0x80042e00` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042e00` | `0x80043114` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043114` | `0x80043448` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043448` | `0x8004379c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x8004379c` | `0x80043b10` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043b10` | `0x80043db8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043db8` | `0x800440c0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800440c0` | `0x8004472c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004472c` | `0x80044cec` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044cec` | `0x8004526c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x8004526c` | `0x80045af8` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045af8` | `0x80045be4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045be4` | `0x80045cb4` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045cb4` | `0x80045f4c` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80045f4c` | `0x800468dc` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x800468dc` | `0x80046eb8` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x80046eb8` | `0x80046ed4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046ed4` | `0x800483f8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800483f8` | `0x80048444` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048444` | `0x80048600` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048600` | `0x800493c8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800493c8` | `0x8004b604` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b604` | `0x8004c70c` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c70c` | `0x8004d36c` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d36c` | `0x8004e174` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e174` | `0x8004edd4` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004edd4` | `0x8004f68c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f68c` | `0x8004ff80` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004ff80` | `0x8005051c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8005051c` | `0x80050bc8` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050bc8` | `0x80050be8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050be8` | `0x80051294` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051294` | `0x800512b4` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x800512b4` | `0x80051be4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051be4` | `0x80051f30` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051f30` | `0x800520a0` | 368 | `h_STOP` | UNCONVERTED |
| `0x800520a0` | `0x800520a4` | 4 | `h_invalid` | UNCONVERTED |
| `0x800520a4` | `0x8005212c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005212c` | `0x80052320` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052320` | `0x80052350` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052350` | `0x80052364` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052364` | `0x80052374` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052374` | `0x800523a4` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x800523a4` | `0x80052598` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052598` | `0x800525c8` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800525c8` | `0x800525dc` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800525dc` | `0x800525ec` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800525ec` | `0x8005261c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x8005261c` | `0x80052640` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052640` | `0x80052670` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052670` | `0x80052864` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052864` | `0x80052894` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052894` | `0x800528a8` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x800528a8` | `0x800528b8` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x800528b8` | `0x800528e8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800528e8` | `0x80052adc` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052adc` | `0x80052b0c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052b0c` | `0x80052b20` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052b20` | `0x80052b30` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052b30` | `0x80052b60` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052b60` | `0x80052d54` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052d54` | `0x80052d84` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052d84` | `0x80052d98` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052d98` | `0x80052da8` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052da8` | `0x80052dd8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052dd8` | `0x80052dd8` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052dd8` | `0x80052df4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052f80` | `0x800531b4` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800536b4` | `0x800537e4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800537e4` | `0x80053840` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053840` | `0x80053860` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053860` | `0x8005399c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053b6c` | `0x80053b78` | 12 | `requests_hash_verify` | TAIL |
