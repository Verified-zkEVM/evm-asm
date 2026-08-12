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

`.text` = [0x80000000, 0x80053d3c), 343356 bytes (`RegionMap.textSizeBytes = 0x53d3c`)

- symbols in `.text`: 906 (449 converted, 457 unconverted)
- covered by converted `_prog`s: 121500 bytes (35.39%)
- NOT covered: 221856 bytes (64.61%), 458 ranges

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
| `0x80015bc8` | `0x800186d0` | 11016 | `block_verdict` | UNCONVERTED |
| `0x800186d0` | `0x80019440` | 3440 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019440` | `0x8001965c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019944` | `0x800199d8` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a1d0` | `0x8001a428` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a428` | `0x8001a6a0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a6a0` | `0x8001a934` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001af24` | `0x8001b240` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b608` | `0x8001b880` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b880` | `0x8001bb24` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bb24` | `0x8001c600` | 2780 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c908` | `0x8001c950` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001cfe0` | `0x8001d1c8` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d1c8` | `0x8001d224` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d224` | `0x8001d2f0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d2f0` | `0x8001d3c4` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d3c4` | `0x8001e2ec` | 3880 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ebc0` | `0x8001ecd4` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ecd4` | `0x8001efdc` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fc90` | `0x8001fcd0` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001ff30` | `0x80020078` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020078` | `0x800200a8` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x800205f8` | `0x80020788` | 400 | `destroy_storage` | UNCONVERTED |
| `0x8002197c` | `0x80021a98` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021a98` | `0x80021c5c` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021c5c` | `0x80021eec` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x800225c0` | `0x800226e0` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x800233e0` | `0x800233fc` | 28 | `keccak_init` | UNCONVERTED |
| `0x800233fc` | `0x80023470` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023470` | `0x800234c0` | 80 | `keccak_final` | UNCONVERTED |
| `0x800234c0` | `0x800234ec` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800234ec` | `0x800235cc` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x800235cc` | `0x8002364c` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x8002364c` | `0x8002367c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x800237bc` | `0x80023880` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023880` | `0x800238d4` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800238d4` | `0x80023904` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023904` | `0x80023944` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023944` | `0x8002397c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002397c` | `0x800239bc` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023b1c` | `0x80023b34` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024af4` | `0x80024cf0` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024d88` | `0x80024e94` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80024ef8` | `0x800250c0` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x800250c0` | `0x800253a8` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x800253a8` | `0x80025490` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025490` | `0x8002556c` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x8002556c` | `0x80025644` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800259c8` | `0x80025aec` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025aec` | `0x80025be4` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x8002640c` | `0x8002641c` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026600` | `0x80026818` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026818` | `0x80026a0c` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026da0` | `0x80027424` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028340` | `0x8002885c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800288bc` | `0x8002895c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x800295a8` | `0x80029d9c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a430` | `0x8002a6cc` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a6cc` | `0x8002a704` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c35c` | `0x8002c854` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c854` | `0x8002d460` | 3084 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d460` | `0x8002da30` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002da30` | `0x8002f3f0` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f3f0` | `0x8002f414` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f414` | `0x8002f430` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f430` | `0x8002f6f4` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f6f4` | `0x8002f704` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f704` | `0x8002f738` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f738` | `0x8002f750` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f750` | `0x8002f760` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f760` | `0x8002f794` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f794` | `0x8002f79c` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f79c` | `0x8002f848` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f848` | `0x8002f854` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f854` | `0x8002f87c` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f87c` | `0x8002f8bc` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f8bc` | `0x8002f8ec` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f8ec` | `0x8002f8ec` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f8ec` | `0x8002f904` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f904` | `0x8002f90c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f90c` | `0x8002f918` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f918` | `0x8002f930` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f930` | `0x8002f948` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f948` | `0x8002f95c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f95c` | `0x8002f97c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f97c` | `0x8002f990` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f990` | `0x8002f9bc` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f9bc` | `0x8002fa04` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fa04` | `0x8002fae4` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fae4` | `0x8002fb94` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fb94` | `0x8002fbb4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fbb4` | `0x8002fc28` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fc28` | `0x8002fc38` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fc38` | `0x8002fc44` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fc44` | `0x8002fd28` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002fd28` | `0x8002fd50` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002fd50` | `0x8002fd64` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002fd64` | `0x8002fd64` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002fd64` | `0x8002fd64` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002fd64` | `0x8002fd84` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002fd84` | `0x8002fdb4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002fdb4` | `0x8002fdd8` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002fdd8` | `0x8002fdf8` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fdf8` | `0x8002fdfc` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fdfc` | `0x8002fe88` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002fe88` | `0x8002fe98` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002fe98` | `0x8002fea8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002fea8` | `0x8002ffd8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002ffd8` | `0x8002ffd8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002ffd8` | `0x80030174` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030174` | `0x80030174` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030174` | `0x800301d4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80030f8c` | `0x80030fb4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80030fb4` | `0x800311c4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800312c4` | `0x80031370` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031370` | `0x800313f4` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800313f4` | `0x80031474` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031474` | `0x8003152c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x8003152c` | `0x800315a0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800315a0` | `0x80031764` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031764` | `0x800317d4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800317d4` | `0x8003184c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x8003184c` | `0x800319fc` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800319fc` | `0x80031a78` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031a78` | `0x80031ac8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031ac8` | `0x80031b18` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031b18` | `0x80031b48` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031b48` | `0x80031b8c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031b8c` | `0x80031bd0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031bd0` | `0x80031c80` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031c80` | `0x80031ddc` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031ddc` | `0x800320d8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800320d8` | `0x800322b4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800322b4` | `0x80032360` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032360` | `0x800324d8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800324d8` | `0x800326a4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800326a4` | `0x800327d8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800328c8` | `0x800329a4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800329a4` | `0x80032af4` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032af4` | `0x80032cd0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80032e80` | `0x8003306c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003306c` | `0x800330c0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800330c0` | `0x80033108` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033108` | `0x800331dc` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800331dc` | `0x800332bc` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800332bc` | `0x80033474` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80033e8c` | `0x80033f08` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80033f08` | `0x80033ff4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034658` | `0x800346c8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800346c8` | `0x80034728` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034b04` | `0x80034b58` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034d20` | `0x80034f8c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80034f8c` | `0x800352cc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800352cc` | `0x8003557c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x8003557c` | `0x800358b0` | 820 | `bng2_double` | UNCONVERTED |
| `0x800358b0` | `0x80035c38` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035c38` | `0x80035d58` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035d78` | `0x800361a8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800361a8` | `0x800365ec` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036640` | `0x800367ec` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036c60` | `0x80036e24` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800375b4` | `0x8003788c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038178` | `0x80038208` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038208` | `0x800382d8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800384b0` | `0x8003850c` | 92 | `blq_sub` | UNCONVERTED |
| `0x800386fc` | `0x80038968` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038968` | `0x80038c88` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038c88` | `0x80038f38` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80038f38` | `0x80039114` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039114` | `0x8003945c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800395a8` | `0x8003ae0c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003ae0c` | `0x8003c048` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c16c` | `0x8003c288` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c298` | `0x8003c2c8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c2c8` | `0x8003c864` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c864` | `0x8003cb74` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cb74` | `0x8003cb7c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cb7c` | `0x8003cb80` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cb80` | `0x8003cd64` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003ce5c` | `0x8003d0a4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d0a4` | `0x8003d708` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d708` | `0x8003d824` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d824` | `0x8003da3c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003da3c` | `0x8003da7c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003da7c` | `0x8003dac4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003dac4` | `0x8003db14` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003db14` | `0x8003db6c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003db6c` | `0x8003dbcc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003dbcc` | `0x8003dc34` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003dc34` | `0x8003dca4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dca4` | `0x8003dd1c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003dd1c` | `0x8003dd9c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003dd9c` | `0x8003de24` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003de24` | `0x8003deb4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003deb4` | `0x8003df4c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003df4c` | `0x8003dfec` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003dfec` | `0x8003e094` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e094` | `0x8003e144` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e144` | `0x8003e1fc` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e1fc` | `0x8003e2bc` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e2bc` | `0x8003e384` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e384` | `0x8003e454` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e454` | `0x8003e52c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e52c` | `0x8003e60c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e60c` | `0x8003e6f4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e6f4` | `0x8003e7e4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e7e4` | `0x8003e8dc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e8dc` | `0x8003e9dc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e9dc` | `0x8003eae4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003eae4` | `0x8003ebf4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003ebf4` | `0x8003ed0c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ed0c` | `0x8003ee2c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003ee2c` | `0x8003ef54` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003ef54` | `0x8003f084` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f084` | `0x8003f1bc` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f1bc` | `0x8003f2fc` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f2fc` | `0x8003f374` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f374` | `0x8003f3ec` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f3ec` | `0x8003f464` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f464` | `0x8003f4dc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f4dc` | `0x8003f554` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f554` | `0x8003f5cc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f5cc` | `0x8003f644` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f644` | `0x8003f6bc` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f6bc` | `0x8003f734` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f734` | `0x8003f7ac` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f7ac` | `0x8003f824` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f824` | `0x8003f89c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f89c` | `0x8003f914` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f914` | `0x8003f98c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f98c` | `0x8003fa04` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fa04` | `0x8003fa7c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fa7c` | `0x8003faec` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003faec` | `0x8003fb5c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fb5c` | `0x8003fbcc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fbcc` | `0x8003fc3c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fc3c` | `0x8003fcac` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003fcac` | `0x8003fd1c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003fd1c` | `0x8003fd8c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003fd8c` | `0x8003fdfc` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fdfc` | `0x8003fe6c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003fe6c` | `0x8003fedc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003fedc` | `0x8003ff4c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003ff4c` | `0x8003ffbc` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003ffbc` | `0x8004002c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004002c` | `0x8004009c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004009c` | `0x8004010c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004010c` | `0x8004017c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004017c` | `0x80040194` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040194` | `0x800401a8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800401a8` | `0x80040234` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040234` | `0x8004024c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004024c` | `0x80040260` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040260` | `0x800402e8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800402e8` | `0x80040300` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040300` | `0x80040314` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040314` | `0x80040334` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040334` | `0x8004033c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004033c` | `0x80040348` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040348` | `0x8004034c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004034c` | `0x800403d0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800403d0` | `0x80040478` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040478` | `0x800405ac` | 308 | `h_MUL` | UNCONVERTED |
| `0x800405ac` | `0x80040654` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040654` | `0x8004074c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8004074c` | `0x800407e4` | 152 | `h_LT` | UNCONVERTED |
| `0x800407e4` | `0x8004087c` | 152 | `h_GT` | UNCONVERTED |
| `0x8004087c` | `0x80040910` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040910` | `0x800409a4` | 148 | `h_SGT` | UNCONVERTED |
| `0x800409a4` | `0x80040a28` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040a28` | `0x80040a88` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040a88` | `0x80040afc` | 116 | `h_AND` | UNCONVERTED |
| `0x80040afc` | `0x80040b70` | 116 | `h_OR` | UNCONVERTED |
| `0x80040b70` | `0x80040be4` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040be4` | `0x80040c44` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040c44` | `0x80040d30` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040d30` | `0x80040ed0` | 416 | `h_SHL` | UNCONVERTED |
| `0x80040ed0` | `0x80041070` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041070` | `0x80041224` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041224` | `0x80041324` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041324` | `0x80041358` | 52 | `h_POP` | UNCONVERTED |
| `0x80041358` | `0x800416d4` | 892 | `h_MLOAD` | UNCONVERTED |
| `0x800416d4` | `0x800419e4` | 784 | `h_MSTORE` | UNCONVERTED |
| `0x800419e4` | `0x80041b1c` | 312 | `h_MSTORE8` | UNCONVERTED |
| `0x80041b1c` | `0x80041b60` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041b60` | `0x80041ba4` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041ba4` | `0x80041bf4` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041bf4` | `0x80041c44` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041c44` | `0x80041c94` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041c94` | `0x80041ce4` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041ce4` | `0x80041d34` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041d34` | `0x80041d84` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041d84` | `0x80041dd4` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041dd4` | `0x80041e24` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041e24` | `0x80041e74` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041e74` | `0x80041ec4` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041ec4` | `0x80041f14` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80041f14` | `0x80041f64` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041f64` | `0x80041fb4` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041fb4` | `0x80042004` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042004` | `0x80042054` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042054` | `0x800420ec` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x800420ec` | `0x800421d8` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x800421d8` | `0x8004221c` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x8004221c` | `0x80042438` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042438` | `0x80042620` | 488 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042620` | `0x80042664` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042664` | `0x80042848` | 484 | `h_CODECOPY` | UNCONVERTED |
| `0x80042848` | `0x80042850` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042850` | `0x80042910` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042910` | `0x80042a04` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042a04` | `0x80042a48` | 68 | `h_PC` | UNCONVERTED |
| `0x80042a48` | `0x80042cd0` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042cd0` | `0x80042fc4` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042fc4` | `0x800432d8` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800432d8` | `0x8004360c` | 820 | `h_LOG2` | UNCONVERTED |
| `0x8004360c` | `0x80043960` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043960` | `0x80043cd4` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043cd4` | `0x80043f7c` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80043f7c` | `0x80044284` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044284` | `0x800448f0` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x800448f0` | `0x80044eb0` | 1472 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044eb0` | `0x80045430` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045430` | `0x80045cbc` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045cbc` | `0x80045da8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045da8` | `0x80045e78` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045e78` | `0x80046110` | 664 | `h_MCOPY` | UNCONVERTED |
| `0x80046110` | `0x80046aa0` | 2448 | `h_RETURN` | UNCONVERTED |
| `0x80046aa0` | `0x8004707c` | 1500 | `h_REVERT` | UNCONVERTED |
| `0x8004707c` | `0x80047098` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047098` | `0x800485bc` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800485bc` | `0x80048608` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048608` | `0x800487c4` | 444 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800487c4` | `0x8004958c` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x8004958c` | `0x8004b7c8` | 8764 | `h_CALL` | UNCONVERTED |
| `0x8004b7c8` | `0x8004c8d0` | 4360 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c8d0` | `0x8004d530` | 3168 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d530` | `0x8004e338` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e338` | `0x8004ef98` | 3168 | `h_STATICCALL` | UNCONVERTED |
| `0x8004ef98` | `0x8004f850` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f850` | `0x80050144` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050144` | `0x800506e0` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800506e0` | `0x80050d8c` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050d8c` | `0x80050dac` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050dac` | `0x80051458` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051458` | `0x80051478` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051478` | `0x80051da8` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051da8` | `0x800520f4` | 844 | `h_EXP` | UNCONVERTED |
| `0x800520f4` | `0x80052264` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052264` | `0x80052268` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052268` | `0x800522f0` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800522f0` | `0x800524e4` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800524e4` | `0x80052514` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052514` | `0x80052528` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052528` | `0x80052538` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052538` | `0x80052568` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052568` | `0x8005275c` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x8005275c` | `0x8005278c` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x8005278c` | `0x800527a0` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800527a0` | `0x800527b0` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800527b0` | `0x800527e0` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800527e0` | `0x80052804` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052804` | `0x80052834` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052834` | `0x80052a28` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052a28` | `0x80052a58` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052a58` | `0x80052a6c` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052a6c` | `0x80052a7c` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052a7c` | `0x80052aac` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052aac` | `0x80052ca0` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052ca0` | `0x80052cd0` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052cd0` | `0x80052ce4` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052ce4` | `0x80052cf4` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052cf4` | `0x80052d24` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052d24` | `0x80052f18` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052f18` | `0x80052f48` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052f48` | `0x80052f5c` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052f5c` | `0x80052f6c` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052f6c` | `0x80052f9c` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052f9c` | `0x80052f9c` | 0 | `.exit_label` | UNCONVERTED |
| `0x80052f9c` | `0x80052fb8` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053144` | `0x80053378` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053878` | `0x800539a8` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800539a8` | `0x80053a04` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053a04` | `0x80053a24` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053a24` | `0x80053b60` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053d30` | `0x80053d3c` | 12 | `requests_hash_verify` | TAIL |
