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

`.text` = [0x80000000, 0x80053668), 341608 bytes (`RegionMap.textSizeBytes = 0x53668`)

- symbols in `.text`: 900 (443 converted, 457 unconverted)
- covered by converted `_prog`s: 119632 bytes (35.02%)
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
| `0x8000d9a0` | `0x8000ecbc` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f0ec` | `0x8000f2cc` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000f2cc` | `0x8000f3b0` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000f3b0` | `0x8000f48c` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000f48c` | `0x8000f520` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000f520` | `0x8000f5dc` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000f5dc` | `0x8000f68c` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000f68c` | `0x8000f770` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x8000f770` | `0x8000f7ac` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8000f7ac` | `0x8000f8dc` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8000f8dc` | `0x8000fa00` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8000fa00` | `0x8000fab0` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x8000fab0` | `0x8000fc2c` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8000fc2c` | `0x8000fd04` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x8000fd04` | `0x8000fe94` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x8000fe94` | `0x80010030` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010030` | `0x800100e0` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800100e0` | `0x80010148` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010148` | `0x800101e4` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x800101e4` | `0x80010818` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80010818` | `0x80010b00` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80010b00` | `0x80010e58` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80010e58` | `0x80011334` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011334` | `0x800115d8` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x800115d8` | `0x800116f4` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x800116f4` | `0x800119ac` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800119ac` | `0x80011bcc` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80011bcc` | `0x80011f64` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80011f64` | `0x80012078` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012078` | `0x80012098` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012098` | `0x80012320` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012320` | `0x80012404` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012404` | `0x800124ac` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800124ac` | `0x80012be0` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80012be0` | `0x80013218` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013554` | `0x80013568` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013568` | `0x80013574` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013574` | `0x800135c4` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x800135c4` | `0x800135e4` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x800135e4` | `0x80013648` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013648` | `0x800138f0` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800138f0` | `0x80013b44` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80013b44` | `0x80013cf8` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800148f8` | `0x80014af0` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80014e10` | `0x80015040` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015430` | `0x80017f2c` | 11004 | `block_verdict` | UNCONVERTED |
| `0x80017f2c` | `0x80018cc0` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80018cc0` | `0x80018edc` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x800191c4` | `0x80019258` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x80019a50` | `0x80019ca8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x80019ca8` | `0x80019f20` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x80019f20` | `0x8001a1b4` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001a7b0` | `0x8001aacc` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001ae94` | `0x8001b10c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b10c` | `0x8001b3b0` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001b3b0` | `0x8001be74` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001c188` | `0x8001c1d0` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001c860` | `0x8001ca48` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001ca48` | `0x8001caa4` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001caa4` | `0x8001cb70` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001cb70` | `0x8001cc44` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001cc44` | `0x8001dbc4` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001e498` | `0x8001e5ac` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001e5ac` | `0x8001e8b4` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001f568` | `0x8001f5a8` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x8001f808` | `0x8001f950` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x8001f950` | `0x8001f980` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x8001fed0` | `0x80020060` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021254` | `0x80021370` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021370` | `0x80021534` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021534` | `0x800217c4` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80021e98` | `0x80021fb8` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80022cb8` | `0x80022cd4` | 28 | `keccak_init` | UNCONVERTED |
| `0x80022cd4` | `0x80022d48` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80022d48` | `0x80022d98` | 80 | `keccak_final` | UNCONVERTED |
| `0x80022d98` | `0x80022dc4` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80022dc4` | `0x80022ea4` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80022ea4` | `0x80022f24` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80022f24` | `0x80022f54` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023094` | `0x80023158` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023158` | `0x800231ac` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x800231ac` | `0x800231dc` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x800231dc` | `0x8002321c` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x8002321c` | `0x80023254` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023254` | `0x80023294` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800233f4` | `0x8002340c` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x800243cc` | `0x800245c8` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024660` | `0x8002476c` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800247d0` | `0x80024998` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80024998` | `0x80024c80` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80024c80` | `0x80024d68` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80024d68` | `0x80024e44` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80024e44` | `0x80024f1c` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x800252d0` | `0x800253f4` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800253f4` | `0x800254ec` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80025d14` | `0x80025d24` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80025f08` | `0x80026120` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026120` | `0x80026314` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x800266a8` | `0x80026d2c` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80027c48` | `0x80028164` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x800281c4` | `0x80028264` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80028eb0` | `0x800296a4` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x80029d38` | `0x80029fd4` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x80029fd4` | `0x8002a00c` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002bc68` | `0x8002c160` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002c160` | `0x8002cd84` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002cd84` | `0x8002d354` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002d354` | `0x8002ed14` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002ed14` | `0x8002ed38` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002ed38` | `0x8002ed54` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002ed54` | `0x8002f018` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f018` | `0x8002f028` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f028` | `0x8002f05c` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f05c` | `0x8002f074` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f074` | `0x8002f084` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f084` | `0x8002f0b8` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f0b8` | `0x8002f0c0` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f0c0` | `0x8002f16c` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002f16c` | `0x8002f178` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002f178` | `0x8002f1a0` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002f1a0` | `0x8002f1e0` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002f1e0` | `0x8002f210` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002f210` | `0x8002f210` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002f210` | `0x8002f228` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002f228` | `0x8002f230` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002f230` | `0x8002f23c` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002f23c` | `0x8002f254` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002f254` | `0x8002f26c` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002f26c` | `0x8002f280` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002f280` | `0x8002f2a0` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002f2a0` | `0x8002f2b4` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002f2b4` | `0x8002f2e0` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002f2e0` | `0x8002f328` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002f328` | `0x8002f408` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002f408` | `0x8002f4b8` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002f4b8` | `0x8002f4d8` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002f4d8` | `0x8002f54c` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002f54c` | `0x8002f55c` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002f55c` | `0x8002f568` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002f568` | `0x8002f64c` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002f64c` | `0x8002f674` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002f674` | `0x8002f688` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002f688` | `0x8002f688` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002f688` | `0x8002f688` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002f688` | `0x8002f6a8` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002f6a8` | `0x8002f6d8` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002f6d8` | `0x8002f6fc` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002f6fc` | `0x8002f71c` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002f71c` | `0x8002f720` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002f720` | `0x8002f7ac` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8002f7ac` | `0x8002f7bc` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8002f7bc` | `0x8002f7cc` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8002f7cc` | `0x8002f8fc` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8002f8fc` | `0x8002f8fc` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8002f8fc` | `0x8002fa98` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x8002fa98` | `0x8002fa98` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x8002fa98` | `0x8002faf8` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x800308b0` | `0x800308d8` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800308d8` | `0x80030ae8` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80030be8` | `0x80030c94` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80030c94` | `0x80030d18` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80030d18` | `0x80030d98` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80030d98` | `0x80030e50` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80030e50` | `0x80030ec4` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80030ec4` | `0x80031088` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031088` | `0x800310f8` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800310f8` | `0x80031170` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031170` | `0x80031320` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031320` | `0x8003139c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003139c` | `0x800313ec` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800313ec` | `0x8003143c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x8003143c` | `0x8003146c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x8003146c` | `0x800314b0` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x800314b0` | `0x800314f4` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800314f4` | `0x800315a4` | 176 | `modexp_mul` | UNCONVERTED |
| `0x800315a4` | `0x80031700` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031700` | `0x800319fc` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800319fc` | `0x80031bd8` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80031bd8` | `0x80031c84` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80031c84` | `0x80031dfc` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80031dfc` | `0x80031fc8` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80031fc8` | `0x800320fc` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x800321ec` | `0x800322c8` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800322c8` | `0x80032418` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032418` | `0x800325f4` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x800327a4` | `0x80032990` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80032990` | `0x800329e4` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800329e4` | `0x80032a2c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80032a2c` | `0x80032b00` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80032b00` | `0x80032be0` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80032be0` | `0x80032d98` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x800337b0` | `0x8003382c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x8003382c` | `0x80033918` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80033f7c` | `0x80033fec` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80033fec` | `0x8003404c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034428` | `0x8003447c` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034644` | `0x800348b0` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x800348b0` | `0x80034bf0` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80034bf0` | `0x80034ea0` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80034ea0` | `0x800351d4` | 820 | `bng2_double` | UNCONVERTED |
| `0x800351d4` | `0x8003555c` | 904 | `bng2_add` | UNCONVERTED |
| `0x8003555c` | `0x8003567c` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x8003569c` | `0x80035acc` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80035acc` | `0x80035f10` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80035f64` | `0x80036110` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036584` | `0x80036748` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80036ed8` | `0x800371b0` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80037a9c` | `0x80037b2c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80037b2c` | `0x80037bfc` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80037dd4` | `0x80037e30` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038020` | `0x8003828c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003828c` | `0x800385ac` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x800385ac` | `0x8003885c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003885c` | `0x80038a38` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80038a38` | `0x80038d80` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80038ecc` | `0x8003a730` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003a730` | `0x8003b96c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003ba90` | `0x8003bbac` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003bbbc` | `0x8003bbec` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003bbec` | `0x8003c188` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003c188` | `0x8003c498` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003c498` | `0x8003c4a0` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003c4a0` | `0x8003c4a4` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003c4a4` | `0x8003c688` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003c780` | `0x8003c9c8` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003c9c8` | `0x8003d02c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d02c` | `0x8003d148` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003d148` | `0x8003d360` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003d360` | `0x8003d3a0` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003d3a0` | `0x8003d3e8` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003d3e8` | `0x8003d438` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003d438` | `0x8003d490` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003d490` | `0x8003d4f0` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003d4f0` | `0x8003d558` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003d558` | `0x8003d5c8` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003d5c8` | `0x8003d640` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003d640` | `0x8003d6c0` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003d6c0` | `0x8003d748` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003d748` | `0x8003d7d8` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003d7d8` | `0x8003d870` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003d870` | `0x8003d910` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003d910` | `0x8003d9b8` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003d9b8` | `0x8003da68` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003da68` | `0x8003db20` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003db20` | `0x8003dbe0` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003dbe0` | `0x8003dca8` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003dca8` | `0x8003dd78` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003dd78` | `0x8003de50` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003de50` | `0x8003df30` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003df30` | `0x8003e018` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e018` | `0x8003e108` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e108` | `0x8003e200` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003e200` | `0x8003e300` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003e300` | `0x8003e408` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003e408` | `0x8003e518` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003e518` | `0x8003e630` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003e630` | `0x8003e750` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003e750` | `0x8003e878` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003e878` | `0x8003e9a8` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003e9a8` | `0x8003eae0` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003eae0` | `0x8003ec20` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003ec20` | `0x8003ec98` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003ec98` | `0x8003ed10` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003ed10` | `0x8003ed88` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003ed88` | `0x8003ee00` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003ee00` | `0x8003ee78` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003ee78` | `0x8003eef0` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003eef0` | `0x8003ef68` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003ef68` | `0x8003efe0` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003efe0` | `0x8003f058` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f058` | `0x8003f0d0` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f0d0` | `0x8003f148` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003f148` | `0x8003f1c0` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003f1c0` | `0x8003f238` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003f238` | `0x8003f2b0` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003f2b0` | `0x8003f328` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003f328` | `0x8003f3a0` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003f3a0` | `0x8003f410` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003f410` | `0x8003f480` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003f480` | `0x8003f4f0` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003f4f0` | `0x8003f560` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003f560` | `0x8003f5d0` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003f5d0` | `0x8003f640` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003f640` | `0x8003f6b0` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003f6b0` | `0x8003f720` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003f720` | `0x8003f790` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8003f790` | `0x8003f800` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x8003f800` | `0x8003f870` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8003f870` | `0x8003f8e0` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x8003f8e0` | `0x8003f950` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8003f950` | `0x8003f9c0` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8003f9c0` | `0x8003fa30` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8003fa30` | `0x8003faa0` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8003faa0` | `0x8003fab8` | 24 | `h_DUPN` | UNCONVERTED |
| `0x8003fab8` | `0x8003facc` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8003facc` | `0x8003fb58` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x8003fb58` | `0x8003fb70` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8003fb70` | `0x8003fb84` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8003fb84` | `0x8003fc0c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8003fc0c` | `0x8003fc24` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x8003fc24` | `0x8003fc38` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x8003fc38` | `0x8003fc58` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x8003fc58` | `0x8003fc60` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8003fc60` | `0x8003fc6c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x8003fc6c` | `0x8003fc70` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8003fc70` | `0x8003fcf4` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x8003fcf4` | `0x8003fd9c` | 168 | `h_ADD` | UNCONVERTED |
| `0x8003fd9c` | `0x8003fed0` | 308 | `h_MUL` | UNCONVERTED |
| `0x8003fed0` | `0x8003ff78` | 168 | `h_SUB` | UNCONVERTED |
| `0x8003ff78` | `0x80040070` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040070` | `0x80040108` | 152 | `h_LT` | UNCONVERTED |
| `0x80040108` | `0x800401a0` | 152 | `h_GT` | UNCONVERTED |
| `0x800401a0` | `0x80040234` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040234` | `0x800402c8` | 148 | `h_SGT` | UNCONVERTED |
| `0x800402c8` | `0x8004034c` | 132 | `h_EQ` | UNCONVERTED |
| `0x8004034c` | `0x800403ac` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x800403ac` | `0x80040420` | 116 | `h_AND` | UNCONVERTED |
| `0x80040420` | `0x80040494` | 116 | `h_OR` | UNCONVERTED |
| `0x80040494` | `0x80040508` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040508` | `0x80040568` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040568` | `0x80040654` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040654` | `0x800407f4` | 416 | `h_SHL` | UNCONVERTED |
| `0x800407f4` | `0x80040994` | 416 | `h_SHR` | UNCONVERTED |
| `0x80040994` | `0x80040b48` | 436 | `h_SAR` | UNCONVERTED |
| `0x80040b48` | `0x80040c48` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80040c48` | `0x80040c7c` | 52 | `h_POP` | UNCONVERTED |
| `0x80040c7c` | `0x80040fc8` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80040fc8` | `0x800412a8` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x800412a8` | `0x800413c8` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800413c8` | `0x8004140c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004140c` | `0x80041450` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041450` | `0x800414a0` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x800414a0` | `0x800414f0` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800414f0` | `0x80041540` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041540` | `0x80041590` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041590` | `0x800415e0` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800415e0` | `0x80041630` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041630` | `0x80041680` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041680` | `0x800416d0` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800416d0` | `0x80041720` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041720` | `0x80041770` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80041770` | `0x800417c0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800417c0` | `0x80041810` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80041810` | `0x80041860` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80041860` | `0x800418b0` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x800418b0` | `0x80041900` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80041900` | `0x80041998` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80041998` | `0x80041a84` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80041a84` | `0x80041ac8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80041ac8` | `0x80041ce4` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80041ce4` | `0x80041eb4` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80041eb4` | `0x80041ef8` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80041ef8` | `0x800420c4` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800420c4` | `0x800420cc` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800420cc` | `0x8004218c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x8004218c` | `0x80042280` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042280` | `0x800422c4` | 68 | `h_PC` | UNCONVERTED |
| `0x800422c4` | `0x8004254c` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x8004254c` | `0x80042840` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80042840` | `0x80042b54` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80042b54` | `0x80042e88` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80042e88` | `0x800431dc` | 852 | `h_LOG3` | UNCONVERTED |
| `0x800431dc` | `0x80043550` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043550` | `0x800437f8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800437f8` | `0x80043b00` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80043b00` | `0x8004416c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x8004416c` | `0x80044714` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044714` | `0x80044c94` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80044c94` | `0x80045520` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045520` | `0x8004560c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x8004560c` | `0x800456dc` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800456dc` | `0x8004595c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x8004595c` | `0x800462f4` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800462f4` | `0x800468d8` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800468d8` | `0x800468f4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800468f4` | `0x80047e18` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80047e18` | `0x80047e64` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80047e64` | `0x80048008` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048008` | `0x80048dd0` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80048dd0` | `0x8004b07c` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b07c` | `0x8004c1f4` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004c1f4` | `0x8004ce58` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004ce58` | `0x8004dc60` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004dc60` | `0x8004e8c4` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004e8c4` | `0x8004f17c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004f17c` | `0x8004fa70` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8004fa70` | `0x8005000c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x8005000c` | `0x800506b8` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x800506b8` | `0x800506d8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800506d8` | `0x80050d84` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80050d84` | `0x80050da4` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80050da4` | `0x800516d4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800516d4` | `0x80051a20` | 844 | `h_EXP` | UNCONVERTED |
| `0x80051a20` | `0x80051b90` | 368 | `h_STOP` | UNCONVERTED |
| `0x80051b90` | `0x80051b94` | 4 | `h_invalid` | UNCONVERTED |
| `0x80051b94` | `0x80051c1c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x80051c1c` | `0x80051e10` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80051e10` | `0x80051e40` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80051e40` | `0x80051e54` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80051e54` | `0x80051e64` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80051e64` | `0x80051e94` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80051e94` | `0x80052088` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052088` | `0x800520b8` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x800520b8` | `0x800520cc` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800520cc` | `0x800520dc` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800520dc` | `0x8005210c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x8005210c` | `0x80052130` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052130` | `0x80052160` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052160` | `0x80052354` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052354` | `0x80052384` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052384` | `0x80052398` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052398` | `0x800523a8` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x800523a8` | `0x800523d8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800523d8` | `0x800525cc` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800525cc` | `0x800525fc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800525fc` | `0x80052610` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052610` | `0x80052620` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052620` | `0x80052650` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052650` | `0x80052844` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80052844` | `0x80052874` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80052874` | `0x80052888` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052888` | `0x80052898` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80052898` | `0x800528c8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800528c8` | `0x800528c8` | 0 | `.exit_label` | UNCONVERTED |
| `0x800528c8` | `0x800528e4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80052a70` | `0x80052ca4` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x800531a4` | `0x800532d4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800532d4` | `0x80053330` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053330` | `0x80053350` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053350` | `0x8005348c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x8005365c` | `0x80053668` | 12 | `requests_hash_verify` | TAIL |
