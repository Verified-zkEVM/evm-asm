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
not linked** (103 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053960), 342368 bytes (`RegionMap.textSizeBytes = 0x53960`)

- symbols in `.text`: 899 (442 converted, 457 unconverted)
- covered by converted `_prog`s: 119248 bytes (34.83%)
- NOT covered: 223120 bytes (65.17%), 458 ranges

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
| `0x800046bc` | `0x80004790` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80004790` | `0x80004864` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004b64` | `0x80004bac` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80004bac` | `0x80004c14` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x80004c14` | `0x80004c6c` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x80004c6c` | `0x80004cd4` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80004cd4` | `0x80004ec8` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x800091a4` | `0x80009368` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009368` | `0x800093d4` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x80009c90` | `0x80009e90` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x80009e90` | `0x80009fd0` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x80009fd0` | `0x8000a28c` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a28c` | `0x8000a37c` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a37c` | `0x8000a4ec` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000d820` | `0x8000eb3c` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000ef6c` | `0x8000f14c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f14c` | `0x8000f230` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f230` | `0x8000f30c` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f30c` | `0x8000f3a0` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f3a0` | `0x8000f45c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000f45c` | `0x8000f50c` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000f50c` | `0x8000f5f0` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000f5f0` | `0x8000f62c` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000f62c` | `0x8000f75c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000f75c` | `0x8000f880` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000f880` | `0x8000f930` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000f930` | `0x8000faac` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8000faac` | `0x8000fb84` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8000fb84` | `0x8000fd14` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8000fd14` | `0x8000feb0` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x8000feb0` | `0x8000ff60` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x8000ff60` | `0x8000ffc8` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x8000ffc8` | `0x80010064` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010064` | `0x80010698` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010698` | `0x80010980` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010980` | `0x80010cd8` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80010cd8` | `0x800111b4` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x800111b4` | `0x80011458` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011458` | `0x80011574` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011574` | `0x8001182c` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x8001182c` | `0x80011a4c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80011a4c` | `0x80011de4` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80011de4` | `0x80011ef8` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80011ef8` | `0x80011f18` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80011f18` | `0x800121a0` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x800121a0` | `0x80012284` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012284` | `0x8001232c` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x8001232c` | `0x80012a60` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80012a60` | `0x80013098` | 1592 | `block_state_root` | UNCONVERTED |
| `0x800133d4` | `0x800133e8` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x800133e8` | `0x800133f4` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800133f4` | `0x80013444` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013444` | `0x80013464` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013464` | `0x800134c8` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x800134c8` | `0x80013770` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80013770` | `0x800139c4` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x800139c4` | `0x80013b78` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80014778` | `0x80014970` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80014c90` | `0x80014ec0` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x800152b0` | `0x80017dac` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80017dac` | `0x80018b40` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80018b40` | `0x80018d5c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019044` | `0x800190d8` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x800198d0` | `0x80019b28` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x80019b28` | `0x80019da0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x80019da0` | `0x8001a034` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a630` | `0x8001a94c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ad14` | `0x8001af8c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001af8c` | `0x8001b230` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b230` | `0x8001bcf4` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c008` | `0x8001c050` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c6e0` | `0x8001c8c8` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001c8c8` | `0x8001c924` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001c924` | `0x8001c9f0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001c9f0` | `0x8001cac4` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cac4` | `0x8001da44` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e318` | `0x8001e42c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e42c` | `0x8001e734` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f3e8` | `0x8001f428` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f688` | `0x8001f7d0` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001f7d0` | `0x8001f800` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001fd50` | `0x8001fee0` | 400 | `destroy_storage` | UNCONVERTED |
| `0x800210d4` | `0x800211f0` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x800211f0` | `0x800213b4` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x800213b4` | `0x80021644` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021d18` | `0x80021e38` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022b38` | `0x80022b54` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022b54` | `0x80022bc8` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022bc8` | `0x80022c18` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022c18` | `0x80022c44` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022c44` | `0x80022d24` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022d24` | `0x80022da4` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80022da4` | `0x80022dd4` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80022f14` | `0x80022fd8` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80022fd8` | `0x8002302c` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x8002302c` | `0x8002305c` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x8002305c` | `0x8002309c` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x8002309c` | `0x800230d4` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x800230d4` | `0x80023114` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023274` | `0x8002328c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x8002424c` | `0x80024448` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x800244e0` | `0x800245ec` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024650` | `0x80024818` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024818` | `0x80024b00` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024b00` | `0x80024be8` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024be8` | `0x80024cc4` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024cc4` | `0x80024d9c` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025150` | `0x80025274` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025274` | `0x8002536c` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025b94` | `0x80025ba4` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025d88` | `0x80025fa0` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80025fa0` | `0x80026194` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026528` | `0x80026bac` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027ac8` | `0x80027fe4` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028044` | `0x800280e4` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028d30` | `0x80029524` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029bb8` | `0x80029e54` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029e54` | `0x80029e8c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002bae8` | `0x8002bfe0` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002bfe0` | `0x8002cc04` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cc04` | `0x8002d1d4` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d1d4` | `0x8002eb94` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002eb94` | `0x8002ebb8` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002ebb8` | `0x8002ebd4` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002ebd4` | `0x8002ee98` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002ee98` | `0x8002eea8` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002eea8` | `0x8002eedc` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002eedc` | `0x8002eef4` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002eef4` | `0x8002ef04` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002ef04` | `0x8002ef38` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002ef38` | `0x8002ef40` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002ef40` | `0x8002efec` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002efec` | `0x8002eff8` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002eff8` | `0x8002f020` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f020` | `0x8002f060` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f060` | `0x8002f090` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f090` | `0x8002f090` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f090` | `0x8002f0a8` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f0a8` | `0x8002f0b0` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f0b0` | `0x8002f0bc` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f0bc` | `0x8002f0d4` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f0d4` | `0x8002f0ec` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f0ec` | `0x8002f100` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f100` | `0x8002f120` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f120` | `0x8002f134` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f134` | `0x8002f160` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f160` | `0x8002f1a8` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f1a8` | `0x8002f288` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f288` | `0x8002f338` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f338` | `0x8002f358` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f358` | `0x8002f3cc` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f3cc` | `0x8002f3dc` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f3dc` | `0x8002f3e8` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f3e8` | `0x8002f4cc` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f4cc` | `0x8002f4f4` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f4f4` | `0x8002f508` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f508` | `0x8002f508` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f508` | `0x8002f508` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f508` | `0x8002f528` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f528` | `0x8002f558` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f558` | `0x8002f57c` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f57c` | `0x8002f59c` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f59c` | `0x8002f5a0` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f5a0` | `0x8002f62c` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f62c` | `0x8002f63c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f63c` | `0x8002f64c` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f64c` | `0x8002f77c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f77c` | `0x8002f77c` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f77c` | `0x8002f918` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002f918` | `0x8002f918` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002f918` | `0x8002f978` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030730` | `0x80030758` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030758` | `0x80030968` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030a68` | `0x80030b14` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030b14` | `0x80030b98` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030b98` | `0x80030c18` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030c18` | `0x80030cd0` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030cd0` | `0x80030d44` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030d44` | `0x80030f08` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80030f08` | `0x80030f78` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80030f78` | `0x80030ff0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80030ff0` | `0x800311a0` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800311a0` | `0x8003121c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003121c` | `0x8003126c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x8003126c` | `0x800312bc` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800312bc` | `0x800312ec` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x800312ec` | `0x80031330` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031330` | `0x80031374` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031374` | `0x80031424` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031424` | `0x80031580` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031580` | `0x8003187c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003187c` | `0x80031a58` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031a58` | `0x80031b04` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031b04` | `0x80031c7c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031c7c` | `0x80031e48` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031e48` | `0x80031f7c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x8003206c` | `0x80032148` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032148` | `0x80032298` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032298` | `0x80032474` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032624` | `0x80032810` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032810` | `0x80032864` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80032864` | `0x800328ac` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800328ac` | `0x80032980` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032980` | `0x80032a60` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032a60` | `0x80032c18` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033630` | `0x800336ac` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800336ac` | `0x80033798` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033dfc` | `0x80033e6c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033e6c` | `0x80033ecc` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800342a8` | `0x800342fc` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800344c4` | `0x80034730` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034730` | `0x80034a70` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034a70` | `0x80034d20` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034d20` | `0x80035054` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035054` | `0x800353dc` | 904 | `bng2_add` | UNCONVERTED |
| `0x800353dc` | `0x800354fc` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x8003551c` | `0x8003594c` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x8003594c` | `0x80035d90` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035de4` | `0x80035f90` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036404` | `0x800365c8` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036d58` | `0x80037030` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003791c` | `0x800379ac` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800379ac` | `0x80037a7c` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037c54` | `0x80037cb0` | 92 | `blq_sub` | UNCONVERTED |
| `0x80037ea0` | `0x8003810c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003810c` | `0x8003842c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003842c` | `0x800386dc` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800386dc` | `0x800388b8` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800388b8` | `0x80038c00` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038d4c` | `0x8003a5b0` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a5b0` | `0x8003b7ec` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003b910` | `0x8003ba2c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003ba3c` | `0x8003ba6c` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003ba6c` | `0x8003c008` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c008` | `0x8003c318` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c318` | `0x8003c320` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c320` | `0x8003c324` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c324` | `0x8003c508` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c600` | `0x8003c848` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c848` | `0x8003ceac` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ceac` | `0x8003cfc8` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003cfc8` | `0x8003d1e0` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d1e0` | `0x8003d220` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d220` | `0x8003d268` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d268` | `0x8003d2b8` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d2b8` | `0x8003d310` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d310` | `0x8003d370` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d370` | `0x8003d3d8` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d3d8` | `0x8003d448` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d448` | `0x8003d4c0` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d4c0` | `0x8003d540` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d540` | `0x8003d5c8` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d5c8` | `0x8003d658` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d658` | `0x8003d6f0` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d6f0` | `0x8003d790` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d790` | `0x8003d838` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d838` | `0x8003d8e8` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003d8e8` | `0x8003d9a0` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003d9a0` | `0x8003da60` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003da60` | `0x8003db28` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003db28` | `0x8003dbf8` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003dbf8` | `0x8003dcd0` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003dcd0` | `0x8003ddb0` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ddb0` | `0x8003de98` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003de98` | `0x8003df88` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003df88` | `0x8003e080` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e080` | `0x8003e180` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e180` | `0x8003e288` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e288` | `0x8003e398` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e398` | `0x8003e4b0` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e4b0` | `0x8003e5d0` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e5d0` | `0x8003e6f8` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e6f8` | `0x8003e828` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e828` | `0x8003e960` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003e960` | `0x8003eaa0` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003eaa0` | `0x8003eb18` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003eb18` | `0x8003eb90` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003eb90` | `0x8003ec08` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003ec08` | `0x8003ec80` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ec80` | `0x8003ecf8` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ecf8` | `0x8003ed70` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003ed70` | `0x8003ede8` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ede8` | `0x8003ee60` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003ee60` | `0x8003eed8` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003eed8` | `0x8003ef50` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003ef50` | `0x8003efc8` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003efc8` | `0x8003f040` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f040` | `0x8003f0b8` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f0b8` | `0x8003f130` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f130` | `0x8003f1a8` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f1a8` | `0x8003f220` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f220` | `0x8003f290` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f290` | `0x8003f300` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f300` | `0x8003f370` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f370` | `0x8003f3e0` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f3e0` | `0x8003f450` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f450` | `0x8003f4c0` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f4c0` | `0x8003f530` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f530` | `0x8003f5a0` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f5a0` | `0x8003f610` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f610` | `0x8003f680` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f680` | `0x8003f6f0` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f6f0` | `0x8003f760` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f760` | `0x8003f7d0` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f7d0` | `0x8003f840` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f840` | `0x8003f8b0` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003f8b0` | `0x8003f920` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003f920` | `0x8003f938` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003f938` | `0x8003f94c` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003f94c` | `0x8003f9d8` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003f9d8` | `0x8003f9f0` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003f9f0` | `0x8003fa04` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003fa04` | `0x8003fa8c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003fa8c` | `0x8003faa4` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003faa4` | `0x8003fab8` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003fab8` | `0x8003fad8` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003fad8` | `0x8003fae0` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003fae0` | `0x8003faec` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003faec` | `0x8003faf0` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003faf0` | `0x8003fb74` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fb74` | `0x8003fc1c` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fc1c` | `0x8003fd50` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fd50` | `0x8003fdf8` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003fdf8` | `0x8003fef0` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8003fef0` | `0x8003ff88` | 152 | `h_LT` | UNCONVERTED |
| `0x8003ff88` | `0x80040020` | 152 | `h_GT` | UNCONVERTED |
| `0x80040020` | `0x800400b4` | 148 | `h_SLT` | UNCONVERTED |
| `0x800400b4` | `0x80040148` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040148` | `0x800401cc` | 132 | `h_EQ` | UNCONVERTED |
| `0x800401cc` | `0x8004022c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004022c` | `0x800402a0` | 116 | `h_AND` | UNCONVERTED |
| `0x800402a0` | `0x80040314` | 116 | `h_OR` | UNCONVERTED |
| `0x80040314` | `0x80040388` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040388` | `0x800403e8` | 96 | `h_NOT` | UNCONVERTED |
| `0x800403e8` | `0x800404d4` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800404d4` | `0x80040674` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040674` | `0x80040814` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040814` | `0x800409c8` | 436 | `h_SAR` | UNCONVERTED |
| `0x800409c8` | `0x80040ac8` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040ac8` | `0x80040afc` | 52 | `h_POP` | UNCONVERTED |
| `0x80040afc` | `0x80040e48` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80040e48` | `0x80041128` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041128` | `0x80041248` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041248` | `0x8004128c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004128c` | `0x800412d0` | 68 | `h_GAS` | UNCONVERTED |
| `0x800412d0` | `0x80041320` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041320` | `0x80041370` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041370` | `0x800413c0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800413c0` | `0x80041410` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041410` | `0x80041460` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041460` | `0x800414b0` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800414b0` | `0x80041500` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041500` | `0x80041550` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041550` | `0x800415a0` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800415a0` | `0x800415f0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800415f0` | `0x80041640` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041640` | `0x80041690` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041690` | `0x800416e0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x800416e0` | `0x80041730` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80041730` | `0x80041780` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041780` | `0x80041818` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041818` | `0x80041904` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041904` | `0x80041948` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041948` | `0x80041b64` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041b64` | `0x80041d34` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041d34` | `0x80041d78` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041d78` | `0x80041f44` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80041f44` | `0x80041f4c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80041f4c` | `0x8004200c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004200c` | `0x80042100` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042100` | `0x80042144` | 68 | `h_PC` | UNCONVERTED |
| `0x80042144` | `0x800423cc` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x800423cc` | `0x800426c0` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800426c0` | `0x800429d4` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800429d4` | `0x80042d08` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042d08` | `0x8004305c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x8004305c` | `0x800433d0` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800433d0` | `0x80043678` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043678` | `0x80043980` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043980` | `0x80043fec` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80043fec` | `0x80044594` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044594` | `0x80044b14` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044b14` | `0x800453a0` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800453a0` | `0x8004548c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x8004548c` | `0x8004555c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x8004555c` | `0x800457dc` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x800457dc` | `0x80046174` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046174` | `0x80046758` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80046758` | `0x80046774` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80046774` | `0x80047c98` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047c98` | `0x80047ce4` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047ce4` | `0x80047e88` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80047e88` | `0x80048c50` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048c50` | `0x8004aefc` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004aefc` | `0x8004c074` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c074` | `0x8004ccd8` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004ccd8` | `0x8004dae0` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004dae0` | `0x8004e744` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e744` | `0x8004effc` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004effc` | `0x8004f8f0` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004f8f0` | `0x8004fe8c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8004fe8c` | `0x80050538` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050538` | `0x80050558` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050558` | `0x80050c04` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050c04` | `0x80050c24` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050c24` | `0x80051554` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051554` | `0x800518a0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800518a0` | `0x80051a10` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051a10` | `0x80051a14` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051a14` | `0x80051a9c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051a9c` | `0x80051c90` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051c90` | `0x80051cc0` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051cc0` | `0x80051cd4` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051cd4` | `0x80051ce4` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051ce4` | `0x80051d14` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051d14` | `0x80051f08` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80051f08` | `0x80051f38` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80051f38` | `0x80051f4c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80051f4c` | `0x80051f5c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80051f5c` | `0x80051f8c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80051f8c` | `0x80051fb0` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80051fb0` | `0x80051fe0` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80051fe0` | `0x800521d4` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800521d4` | `0x80052204` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052204` | `0x80052218` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052218` | `0x80052228` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052228` | `0x80052258` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052258` | `0x8005244c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005244c` | `0x8005247c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x8005247c` | `0x80052490` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052490` | `0x800524a0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800524a0` | `0x800524d0` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800524d0` | `0x800526c4` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800526c4` | `0x800526f4` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800526f4` | `0x80052708` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052708` | `0x80052718` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052718` | `0x80052748` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052748` | `0x80052748` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052748` | `0x80052764` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x800528f0` | `0x80052b24` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053024` | `0x80053154` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053154` | `0x800531b0` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800531b0` | `0x800531d0` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800531d0` | `0x8005330c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x800534dc` | `0x80053960` | 1156 | `requests_hash_verify` | TAIL |
