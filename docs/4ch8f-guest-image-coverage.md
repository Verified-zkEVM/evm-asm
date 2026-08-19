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
not linked** (102 of 545 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80053f44), 343876 bytes (`RegionMap.textSizeBytes = 0x53f44`)

- symbols in `.text`: 907 (443 converted, 464 unconverted)
- covered by converted `_prog`s: 120580 bytes (35.06%)
- NOT covered: 223296 bytes (64.94%), 465 ranges

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
| `0x80000000` | `0x800018c0` | 6336 | `_start` | UNCONVERTED |
| `0x800020c0` | `0x800020f0` | 48 | `sg_load_u32le` | UNCONVERTED |
| `0x800020f0` | `0x80002110` | 32 | `sg_memcpy` | UNCONVERTED |
| `0x80002110` | `0x80002134` | 36 | `sg_validate_fixed_list` | UNCONVERTED |
| `0x80002134` | `0x800021ec` | 184 | `sg_validate_var_list` | UNCONVERTED |
| `0x800021ec` | `0x800022d8` | 236 | `sg_validate_execution_payload` | UNCONVERTED |
| `0x800022d8` | `0x80002410` | 312 | `sg_validate_execution_requests` | UNCONVERTED |
| `0x80002410` | `0x800024e0` | 208 | `sg_validate_npr` | UNCONVERTED |
| `0x800024e0` | `0x800025ac` | 204 | `sg_validate_witness` | UNCONVERTED |
| `0x800025ac` | `0x800026c0` | 276 | `sg_validate_chain_config` | UNCONVERTED |
| `0x800026c0` | `0x800028f0` | 560 | `ssz_htr_withdrawals` | UNCONVERTED |
| `0x800028f0` | `0x80002954` | 100 | `sg_htr_bv48` | UNCONVERTED |
| `0x80002954` | `0x800029ac` | 88 | `sg_htr_bv96` | UNCONVERTED |
| `0x800029ac` | `0x80002a8c` | 224 | `sg_htr_deposit` | UNCONVERTED |
| `0x80002a8c` | `0x80002b40` | 180 | `sg_htr_wr` | UNCONVERTED |
| `0x80002b40` | `0x80002bd8` | 152 | `sg_htr_cr` | UNCONVERTED |
| `0x80002bd8` | `0x80002c88` | 176 | `sg_htr_bd` | UNCONVERTED |
| `0x80002c88` | `0x80002d0c` | 132 | `sg_htr_be` | UNCONVERTED |
| `0x80002d0c` | `0x80002e0c` | 256 | `sg_htr_clist` | UNCONVERTED |
| `0x80002e0c` | `0x80002f84` | 376 | `ssz_htr_execution_requests` | UNCONVERTED |
| `0x80004b34` | `0x80004c08` | 212 | `rlp_item_span` | UNCONVERTED |
| `0x80004c08` | `0x80004cdc` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004fdc` | `0x80005024` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80005024` | `0x8000508c` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x8000508c` | `0x800050e4` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x800050e4` | `0x8000514c` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x8000514c` | `0x80005340` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x8000961c` | `0x800097e0` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x800097e0` | `0x8000984c` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a108` | `0x8000a308` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a308` | `0x8000a448` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a448` | `0x8000a704` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000a704` | `0x8000a7f4` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000a7f4` | `0x8000a964` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e260` | `0x8000f57c` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000f9ac` | `0x8000fb8c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000fb8c` | `0x8000fc70` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fc70` | `0x8000fd4c` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x8000fd4c` | `0x8000fde0` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8000fde0` | `0x8000fe9c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8000fe9c` | `0x8000ff4c` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x8000ff4c` | `0x80010030` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x80010030` | `0x8001006c` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x8001006c` | `0x8001019c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001019c` | `0x800102c0` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x800102c0` | `0x80010370` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010370` | `0x800104ec` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x800104ec` | `0x800105c4` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x800105c4` | `0x80010754` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010754` | `0x800108f0` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x800108f0` | `0x800109a0` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x800109a0` | `0x80010a08` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010a08` | `0x80010aa4` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010aa4` | `0x800110d8` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x800110d8` | `0x800113c0` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x800113c0` | `0x80011718` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011718` | `0x80011bf4` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011bf4` | `0x80011e98` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80011e98` | `0x80011fb4` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80011fb4` | `0x8001226c` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x8001226c` | `0x8001248c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x8001248c` | `0x80012824` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012824` | `0x80012938` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012938` | `0x80012958` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012958` | `0x80012be0` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012be0` | `0x80012cc4` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80012cc4` | `0x80012d6c` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x80012d6c` | `0x800134a0` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x800134a0` | `0x80013ad8` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80013e14` | `0x80013e28` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x80013e28` | `0x80013e34` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x80013e34` | `0x80013e84` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80013e84` | `0x80013ea4` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80013ea4` | `0x80013f08` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80013f08` | `0x800141b0` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x800141b0` | `0x80014404` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014404` | `0x800145b8` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x800151b8` | `0x800153b0` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x800156d0` | `0x80015900` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80015cf0` | `0x800187ec` | 11004 | `block_verdict` | UNCONVERTED |
| `0x800187ec` | `0x80019580` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019580` | `0x8001979c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019a84` | `0x80019b18` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a310` | `0x8001a568` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a568` | `0x8001a7e0` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001a7e0` | `0x8001aa74` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b070` | `0x8001b38c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001b754` | `0x8001b9cc` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001b9cc` | `0x8001bc70` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001bc70` | `0x8001c734` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001ca48` | `0x8001ca90` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d120` | `0x8001d308` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d308` | `0x8001d364` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d364` | `0x8001d430` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d430` | `0x8001d504` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d504` | `0x8001e484` | 3968 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001ed58` | `0x8001ee6c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001ee6c` | `0x8001f174` | 776 | `seed_tx_access_list` | UNCONVERTED |
| `0x8001fe28` | `0x8001fe68` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x800200c8` | `0x80020210` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x80020210` | `0x80020240` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020790` | `0x80020920` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021b14` | `0x80021c30` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80021c30` | `0x80021df4` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x80021df4` | `0x80022084` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022758` | `0x80022878` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023594` | `0x800235b0` | 28 | `keccak_init` | UNCONVERTED |
| `0x800235b0` | `0x80023624` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023624` | `0x80023674` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023674` | `0x800236a0` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x800236a0` | `0x80023780` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023780` | `0x80023800` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023800` | `0x80023830` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023970` | `0x80023a34` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023a34` | `0x80023a88` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023a88` | `0x80023ab8` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023ab8` | `0x80023af8` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023af8` | `0x80023b30` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x80023b30` | `0x80023b70` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x80023cd0` | `0x80023ce8` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80024ca8` | `0x80024ea4` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80024f3c` | `0x80025048` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x800250ac` | `0x80025274` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80025274` | `0x8002555c` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x8002555c` | `0x80025644` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025644` | `0x80025720` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025720` | `0x800257f8` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80025bac` | `0x80025cd0` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x80025cd0` | `0x80025dc8` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x800265f0` | `0x80026600` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x800267e4` | `0x800269fc` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x800269fc` | `0x80026bf0` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80026f84` | `0x80027608` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028524` | `0x80028a40` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028aa0` | `0x80028b40` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x8002978c` | `0x80029f80` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002a614` | `0x8002a8b0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002a8b0` | `0x8002a8e8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c544` | `0x8002ca3c` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002ca3c` | `0x8002d660` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002d660` | `0x8002dc30` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002dc30` | `0x8002f5f0` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002f5f0` | `0x8002f614` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002f614` | `0x8002f630` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002f630` | `0x8002f8f4` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002f8f4` | `0x8002f904` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002f904` | `0x8002f938` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002f938` | `0x8002f950` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002f950` | `0x8002f960` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002f960` | `0x8002f994` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002f994` | `0x8002f99c` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002f99c` | `0x8002fa48` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002fa48` | `0x8002fa54` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002fa54` | `0x8002fa7c` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002fa7c` | `0x8002fabc` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002fabc` | `0x8002faec` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002faec` | `0x8002faec` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002faec` | `0x8002fb04` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fb04` | `0x8002fb0c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fb0c` | `0x8002fb18` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002fb18` | `0x8002fb30` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002fb30` | `0x8002fb48` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002fb48` | `0x8002fb5c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002fb5c` | `0x8002fb7c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8002fb7c` | `0x8002fb90` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8002fb90` | `0x8002fbbc` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8002fbbc` | `0x8002fc04` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x8002fc04` | `0x8002fce4` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x8002fce4` | `0x8002fd94` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8002fd94` | `0x8002fdb4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8002fdb4` | `0x8002fe28` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x8002fe28` | `0x8002fe38` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe44` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8002fe44` | `0x8002ff28` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x8002ff28` | `0x8002ff50` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8002ff50` | `0x8002ff64` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8002ff64` | `0x8002ff64` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8002ff64` | `0x8002ff64` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8002ff64` | `0x8002ff84` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8002ff84` | `0x8002ffb4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8002ffb4` | `0x8002ffd8` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x8002ffd8` | `0x8002fff8` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x8002fff8` | `0x8002fffc` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8002fffc` | `0x80030088` | 140 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030088` | `0x80030098` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030098` | `0x800300a8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800300a8` | `0x800301d8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800301d8` | `0x800301d8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800301d8` | `0x80030374` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030374` | `0x80030374` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030374` | `0x800303d4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8003118c` | `0x800311b4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800311b4` | `0x800313c4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800314c4` | `0x80031570` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031570` | `0x800315f4` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x800315f4` | `0x80031674` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031674` | `0x8003172c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x8003172c` | `0x800317a0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x800317a0` | `0x80031964` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031964` | `0x800319d4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x800319d4` | `0x80031a4c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031a4c` | `0x80031bfc` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80031bfc` | `0x80031c78` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80031c78` | `0x80031cc8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x80031cc8` | `0x80031d18` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80031d18` | `0x80031d48` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80031d48` | `0x80031d8c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80031d8c` | `0x80031dd0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80031dd0` | `0x80031e80` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80031e80` | `0x80031fdc` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80031fdc` | `0x800322d8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800322d8` | `0x800324b4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800324b4` | `0x80032560` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032560` | `0x800326d8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x800326d8` | `0x800328a4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x800328a4` | `0x800329d8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032ac8` | `0x80032ba4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80032ba4` | `0x80032cf4` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80032cf4` | `0x80032ed0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033080` | `0x8003326c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003326c` | `0x800332c0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800332c0` | `0x80033308` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033308` | `0x800333dc` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800333dc` | `0x800334bc` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800334bc` | `0x80033674` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x8003408c` | `0x80034108` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034108` | `0x800341f4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034858` | `0x800348c8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x800348c8` | `0x80034928` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80034d04` | `0x80034d58` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80034f20` | `0x8003518c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x8003518c` | `0x800354cc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800354cc` | `0x8003577c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x8003577c` | `0x80035ab0` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035ab0` | `0x80035e38` | 904 | `bng2_add` | UNCONVERTED |
| `0x80035e38` | `0x80035f58` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80035f78` | `0x800363a8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800363a8` | `0x800367ec` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036840` | `0x800369ec` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80036e60` | `0x80037024` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x800377b4` | `0x80037a8c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038378` | `0x80038408` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038408` | `0x800384d8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x800386b0` | `0x8003870c` | 92 | `blq_sub` | UNCONVERTED |
| `0x800388fc` | `0x80038b68` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80038b68` | `0x80038e88` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80038e88` | `0x80039138` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039138` | `0x80039314` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039314` | `0x8003965c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x800397a8` | `0x8003b00c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b00c` | `0x8003c248` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c36c` | `0x8003c488` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c498` | `0x8003c4c8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c4c8` | `0x8003ca64` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003ca64` | `0x8003cd74` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003cd74` | `0x8003cd7c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003cd7c` | `0x8003cd80` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003cd80` | `0x8003cf64` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d05c` | `0x8003d2a4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d2a4` | `0x8003d908` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003d908` | `0x8003da24` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003da24` | `0x8003dc3c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003dc3c` | `0x8003dc7c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003dc7c` | `0x8003dcc4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003dcc4` | `0x8003dd14` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003dd14` | `0x8003dd6c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003dd6c` | `0x8003ddcc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003ddcc` | `0x8003de34` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003de34` | `0x8003dea4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003dea4` | `0x8003df1c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003df1c` | `0x8003df9c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003df9c` | `0x8003e024` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e024` | `0x8003e0b4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e0b4` | `0x8003e14c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e14c` | `0x8003e1ec` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e1ec` | `0x8003e294` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e294` | `0x8003e344` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e344` | `0x8003e3fc` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e3fc` | `0x8003e4bc` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e4bc` | `0x8003e584` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003e584` | `0x8003e654` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003e654` | `0x8003e72c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003e72c` | `0x8003e80c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003e80c` | `0x8003e8f4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003e8f4` | `0x8003e9e4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003e9e4` | `0x8003eadc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003eadc` | `0x8003ebdc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003ebdc` | `0x8003ece4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003ece4` | `0x8003edf4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003edf4` | `0x8003ef0c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003ef0c` | `0x8003f02c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f02c` | `0x8003f154` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f154` | `0x8003f284` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f284` | `0x8003f3bc` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f3bc` | `0x8003f4fc` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f4fc` | `0x8003f574` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003f574` | `0x8003f5ec` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003f5ec` | `0x8003f664` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003f664` | `0x8003f6dc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003f6dc` | `0x8003f754` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003f754` | `0x8003f7cc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003f7cc` | `0x8003f844` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003f844` | `0x8003f8bc` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003f8bc` | `0x8003f934` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003f934` | `0x8003f9ac` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003f9ac` | `0x8003fa24` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003fa24` | `0x8003fa9c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003fa9c` | `0x8003fb14` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003fb14` | `0x8003fb8c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8003fb8c` | `0x8003fc04` | 120 | `h_DUP15` | UNCONVERTED |
| `0x8003fc04` | `0x8003fc7c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8003fc7c` | `0x8003fcec` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x8003fcec` | `0x8003fd5c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8003fd5c` | `0x8003fdcc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x8003fdcc` | `0x8003fe3c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8003fe3c` | `0x8003feac` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8003feac` | `0x8003ff1c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8003ff1c` | `0x8003ff8c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8003ff8c` | `0x8003fffc` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x8003fffc` | `0x8004006c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8004006c` | `0x800400dc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800400dc` | `0x8004014c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004014c` | `0x800401bc` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x800401bc` | `0x8004022c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004022c` | `0x8004029c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004029c` | `0x8004030c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004030c` | `0x8004037c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004037c` | `0x80040394` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040394` | `0x800403a8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800403a8` | `0x80040434` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040434` | `0x8004044c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004044c` | `0x80040460` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040460` | `0x800404e8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800404e8` | `0x80040500` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040500` | `0x80040514` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040514` | `0x80040534` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040534` | `0x8004053c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x8004053c` | `0x80040548` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040548` | `0x8004054c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x8004054c` | `0x800405d0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x800405d0` | `0x80040678` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040678` | `0x800407ac` | 308 | `h_MUL` | UNCONVERTED |
| `0x800407ac` | `0x80040854` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040854` | `0x8004094c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x8004094c` | `0x800409e4` | 152 | `h_LT` | UNCONVERTED |
| `0x800409e4` | `0x80040a7c` | 152 | `h_GT` | UNCONVERTED |
| `0x80040a7c` | `0x80040b10` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040b10` | `0x80040ba4` | 148 | `h_SGT` | UNCONVERTED |
| `0x80040ba4` | `0x80040c28` | 132 | `h_EQ` | UNCONVERTED |
| `0x80040c28` | `0x80040c88` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80040c88` | `0x80040cfc` | 116 | `h_AND` | UNCONVERTED |
| `0x80040cfc` | `0x80040d70` | 116 | `h_OR` | UNCONVERTED |
| `0x80040d70` | `0x80040de4` | 116 | `h_XOR` | UNCONVERTED |
| `0x80040de4` | `0x80040e44` | 96 | `h_NOT` | UNCONVERTED |
| `0x80040e44` | `0x80040f30` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80040f30` | `0x800410d0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800410d0` | `0x80041270` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041270` | `0x80041424` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041424` | `0x80041524` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041524` | `0x80041558` | 52 | `h_POP` | UNCONVERTED |
| `0x80041558` | `0x800418a4` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x800418a4` | `0x80041b84` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80041b84` | `0x80041ca4` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80041ca4` | `0x80041ce8` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x80041ce8` | `0x80041d2c` | 68 | `h_GAS` | UNCONVERTED |
| `0x80041d2c` | `0x80041d7c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80041d7c` | `0x80041dcc` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80041dcc` | `0x80041e1c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80041e1c` | `0x80041e6c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80041e6c` | `0x80041ebc` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80041ebc` | `0x80041f0c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80041f0c` | `0x80041f5c` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80041f5c` | `0x80041fac` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80041fac` | `0x80041ffc` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80041ffc` | `0x8004204c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004204c` | `0x8004209c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x8004209c` | `0x800420ec` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800420ec` | `0x8004213c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004213c` | `0x8004218c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x8004218c` | `0x800421dc` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800421dc` | `0x80042274` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042274` | `0x80042360` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042360` | `0x800423a4` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800423a4` | `0x800425c0` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x800425c0` | `0x80042790` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042790` | `0x800427d4` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x800427d4` | `0x800429a0` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x800429a0` | `0x800429a8` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x800429a8` | `0x80042a68` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042a68` | `0x80042b5c` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80042b5c` | `0x80042ba0` | 68 | `h_PC` | UNCONVERTED |
| `0x80042ba0` | `0x80042e28` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80042e28` | `0x8004311c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004311c` | `0x80043430` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043430` | `0x80043764` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043764` | `0x80043ab8` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043ab8` | `0x80043e2c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80043e2c` | `0x800440d4` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800440d4` | `0x800443dc` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800443dc` | `0x80044a48` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044a48` | `0x80044ff0` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80044ff0` | `0x80045570` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045570` | `0x80045dfc` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80045dfc` | `0x80045ee8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x80045ee8` | `0x80045fb8` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x80045fb8` | `0x80046238` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046238` | `0x80046bd0` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80046bd0` | `0x800471b4` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800471b4` | `0x800471d0` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800471d0` | `0x800486f4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x800486f4` | `0x80048740` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048740` | `0x800488e4` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x800488e4` | `0x800496ac` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x800496ac` | `0x8004b958` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004b958` | `0x8004cad0` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cad0` | `0x8004d734` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004d734` | `0x8004e53c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e53c` | `0x8004f1a0` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f1a0` | `0x8004fa58` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fa58` | `0x8005034c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005034c` | `0x800508e8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x800508e8` | `0x80050f94` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80050f94` | `0x80050fb4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80050fb4` | `0x80051660` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051660` | `0x80051680` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051680` | `0x80051fb0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80051fb0` | `0x800522fc` | 844 | `h_EXP` | UNCONVERTED |
| `0x800522fc` | `0x8005246c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005246c` | `0x80052470` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052470` | `0x800524f8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800524f8` | `0x800526ec` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x800526ec` | `0x8005271c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x8005271c` | `0x80052730` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052730` | `0x80052740` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052740` | `0x80052770` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052770` | `0x80052964` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052964` | `0x80052994` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052994` | `0x800529a8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x800529a8` | `0x800529b8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x800529b8` | `0x800529e8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x800529e8` | `0x80052a0c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052a0c` | `0x80052a3c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052a3c` | `0x80052c30` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80052c30` | `0x80052c60` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80052c60` | `0x80052c74` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c74` | `0x80052c84` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80052c84` | `0x80052cb4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80052cb4` | `0x80052ea8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80052ea8` | `0x80052ed8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x80052ed8` | `0x80052eec` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80052eec` | `0x80052efc` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80052efc` | `0x80052f2c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80052f2c` | `0x80053120` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053120` | `0x80053150` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053150` | `0x80053164` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053164` | `0x80053174` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053174` | `0x800531a4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800531a4` | `0x800531a4` | 0 | `.exit_label` | UNCONVERTED |
| `0x800531a4` | `0x800531c0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005334c` | `0x80053580` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053a80` | `0x80053bb0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80053bb0` | `0x80053c0c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80053c0c` | `0x80053c2c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80053c2c` | `0x80053d68` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80053f38` | `0x80053f44` | 12 | `requests_hash_verify` | TAIL |
