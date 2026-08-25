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
not linked** (101 of 544 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80054434), 345140 bytes (`RegionMap.textSizeBytes = 0x54434`)

- symbols in `.text`: 909 (443 converted, 466 unconverted)
- covered by converted `_prog`s: 120872 bytes (35.02%)
- NOT covered: 224268 bytes (64.98%), 467 ranges

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
| `0x80004c18` | `0x80004cec` | 212 | `rlp_walk_init` | UNCONVERTED |
| `0x80004fe0` | `0x80005188` | 424 | `rlp_recursive_decode` | UNCONVERTED |
| `0x80005188` | `0x800052fc` | 372 | `rlp_recursive_decode_items` | UNCONVERTED |
| `0x800052fc` | `0x80005320` | 36 | `rlp_recursive_decode_read_be` | UNCONVERTED |
| `0x80005320` | `0x80005368` | 72 | `rlp_content_to_u64` | UNCONVERTED |
| `0x80005368` | `0x800053d0` | 104 | `rlp_content_to_u256_be` | UNCONVERTED |
| `0x800053d0` | `0x80005428` | 88 | `rlp_content_to_u64_strict` | UNCONVERTED |
| `0x80005428` | `0x80005490` | 104 | `rlp_content_to_u256_be_strict` | UNCONVERTED |
| `0x80005490` | `0x80005684` | 500 | `mpt_leaf_node_encode_from_nibbles` | UNCONVERTED |
| `0x8000999c` | `0x80009b60` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009b60` | `0x80009bcc` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a488` | `0x8000a688` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a688` | `0x8000a7c8` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a7c8` | `0x8000aa84` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000aa84` | `0x8000ab74` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ab74` | `0x8000ace4` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e5e0` | `0x8000f8fc` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fd2c` | `0x8000ff0c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000ff0c` | `0x8000fff0` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fff0` | `0x800100cc` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x800100cc` | `0x80010160` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010160` | `0x8001021c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8001021c` | `0x800102cc` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x800102cc` | `0x800103b0` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x800103b0` | `0x800103ec` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103ec` | `0x8001051c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001051c` | `0x80010640` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010640` | `0x800106f0` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106f0` | `0x8001086c` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8001086c` | `0x80010944` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010944` | `0x80010ad4` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010ad4` | `0x80010c70` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c70` | `0x80010d20` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010d20` | `0x80010d88` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d88` | `0x80010e24` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010e24` | `0x80011458` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011458` | `0x80011740` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011740` | `0x80011a98` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011a98` | `0x80011f74` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f74` | `0x80012218` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80012218` | `0x80012334` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80012334` | `0x800125ec` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125ec` | `0x8001280c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x8001280c` | `0x80012ba4` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012ba4` | `0x80012cb8` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012cb8` | `0x80012cd8` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012cd8` | `0x80012f60` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f60` | `0x80013044` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80013044` | `0x800130ec` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130ec` | `0x80013820` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013820` | `0x80013e58` | 1592 | `block_state_root` | UNCONVERTED |
| `0x80014194` | `0x800141a8` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x800141a8` | `0x800141b4` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800141b4` | `0x80014204` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80014204` | `0x80014224` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80014224` | `0x80014288` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014288` | `0x80014530` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014530` | `0x80014784` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014784` | `0x80014938` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015538` | `0x80015730` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a50` | `0x80015c80` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016070` | `0x80018b7c` | 11020 | `block_verdict` | UNCONVERTED |
| `0x80018b7c` | `0x80019910` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019910` | `0x80019b2c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x80019e14` | `0x80019ea8` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001a6a0` | `0x8001a8f8` | 600 | `tx_extract_to_address` | UNCONVERTED |
| `0x8001a8f8` | `0x8001ab70` | 632 | `tx_extract_value` | UNCONVERTED |
| `0x8001ab70` | `0x8001ae04` | 660 | `tx_extract_data_section` | UNCONVERTED |
| `0x8001b400` | `0x8001b71c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001bae4` | `0x8001bd5c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd5c` | `0x8001c000` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001c000` | `0x8001cac4` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cdd8` | `0x8001ce20` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d4c0` | `0x8001d6a8` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d6a8` | `0x8001d704` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d704` | `0x8001d7d0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7d0` | `0x8001d8a4` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d8a4` | `0x8001e834` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f108` | `0x8001f21c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f21c` | `0x8001f650` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x80020304` | `0x80020344` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x800205a4` | `0x800206ec` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800206ec` | `0x8002071c` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c6c` | `0x80020dfc` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021ff0` | `0x8002210c` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x8002210c` | `0x800222d0` | 452 | `account_writes_block_upsert` | UNCONVERTED |
| `0x800222d0` | `0x80022560` | 656 | `account_writes_apply_deletes` | UNCONVERTED |
| `0x80022c34` | `0x80022d54` | 288 | `account_writes_undo_push` | UNCONVERTED |
| `0x80023a70` | `0x80023a8c` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a8c` | `0x80023b00` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023b00` | `0x80023b50` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b50` | `0x80023b7c` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b7c` | `0x80023c5c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c5c` | `0x80023cdc` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023cdc` | `0x80023d0c` | 48 | `bal_rlp_measure_into_throwaway` | UNCONVERTED |
| `0x80023e4c` | `0x80023f10` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023f10` | `0x80023f64` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f64` | `0x80023f94` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80023f94` | `0x80023fd4` | 64 | `bal_serializer_addr_matches` | UNCONVERTED |
| `0x80023fd4` | `0x8002400c` | 56 | `bal_serializer_addr_matches_be` | UNCONVERTED |
| `0x8002400c` | `0x8002404c` | 64 | `bal_serializer_slot_eq` | UNCONVERTED |
| `0x800241ac` | `0x800241c4` | 24 | `bal_serializer_u64_to_field` | UNCONVERTED |
| `0x80025184` | `0x80025380` | 508 | `bal_serializer_rebuild_hash` | UNCONVERTED |
| `0x80025418` | `0x80025524` | 268 | `bal_builder_ensure_account` | UNCONVERTED |
| `0x80025588` | `0x80025750` | 456 | `bal_builder_record_storage_change` | UNCONVERTED |
| `0x80025750` | `0x80025a38` | 744 | `bal_emit_storage_changes` | UNCONVERTED |
| `0x80025a38` | `0x80025b20` | 232 | `bal_builder_append_balance` | UNCONVERTED |
| `0x80025b20` | `0x80025bfc` | 220 | `bal_builder_append_nonce` | UNCONVERTED |
| `0x80025bfc` | `0x80025cd4` | 216 | `bal_builder_append_code` | UNCONVERTED |
| `0x80026088` | `0x800261ac` | 292 | `read_sets_merge_one` | UNCONVERTED |
| `0x800261ac` | `0x800262a4` | 248 | `read_sets_incorporate_tx` | UNCONVERTED |
| `0x80026acc` | `0x80026adc` | 16 | `eip8037_tx_state_gas` | UNCONVERTED |
| `0x80026cc0` | `0x80026ed8` | 536 | `tx_extract_nonce_and_gas` | UNCONVERTED |
| `0x80026ed8` | `0x800270cc` | 500 | `tx_extract_gas_pricing` | UNCONVERTED |
| `0x80027460` | `0x80027ae4` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028a00` | `0x80028f1c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x80028f7c` | `0x8002901c` | 160 | `eip7778_remaining_block_gas_check` | UNCONVERTED |
| `0x80029c68` | `0x8002a45c` | 2036 | `eip7702_auth_state_prepare` | UNCONVERTED |
| `0x8002aaf0` | `0x8002ad8c` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad8c` | `0x8002adc4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ca20` | `0x8002cf18` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cf18` | `0x8002db3c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db3c` | `0x8002e10c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e10c` | `0x8002facc` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002facc` | `0x8002faf0` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002faf0` | `0x8002fb0c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fb0c` | `0x8002fdd0` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fdd0` | `0x8002fde0` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fde0` | `0x8002fe14` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fe14` | `0x8002fe2c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe2c` | `0x8002fe3c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe3c` | `0x8002fe70` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe70` | `0x8002fe78` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe78` | `0x8002ff24` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ff24` | `0x8002ff30` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff30` | `0x8002ff58` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff58` | `0x8002ff98` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff98` | `0x8002ffc8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffc8` | `0x8002ffc8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffc8` | `0x8002ffe0` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ffe0` | `0x8002ffe8` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ffe8` | `0x8002fff4` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002fff4` | `0x8003000c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8003000c` | `0x80030024` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030024` | `0x80030038` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030038` | `0x80030058` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030058` | `0x8003006c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8003006c` | `0x80030098` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x80030098` | `0x800300e0` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300e0` | `0x800301c0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x800301c0` | `0x80030270` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030270` | `0x80030290` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030290` | `0x80030304` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030304` | `0x80030314` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030314` | `0x80030320` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x80030320` | `0x80030404` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030404` | `0x8003042c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8003042c` | `0x80030440` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030440` | `0x80030440` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030440` | `0x80030440` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030440` | `0x80030460` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030460` | `0x80030490` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030490` | `0x800304b4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x800304b4` | `0x800304d4` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304d4` | `0x800304d8` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304d8` | `0x80030578` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030578` | `0x80030588` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030588` | `0x80030598` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x80030598` | `0x800306c8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306c8` | `0x800306c8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306c8` | `0x80030864` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030864` | `0x80030864` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030864` | `0x800308c4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8003167c` | `0x800316a4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800316a4` | `0x800318b4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800319b4` | `0x80031a60` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a60` | `0x80031ae4` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031ae4` | `0x80031b64` | 128 | `account_state_created_contains` | UNCONVERTED |
| `0x80031b64` | `0x80031c1c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031c1c` | `0x80031c90` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c90` | `0x80031e54` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e54` | `0x80031ec4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031ec4` | `0x80031f3c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f3c` | `0x800320ec` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320ec` | `0x80032168` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032168` | `0x800321b8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800321b8` | `0x80032208` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80032208` | `0x80032238` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032238` | `0x8003227c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x8003227c` | `0x800322c0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800322c0` | `0x80032370` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032370` | `0x800324cc` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324cc` | `0x800327c8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327c8` | `0x800329a4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800329a4` | `0x80032a50` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a50` | `0x80032bc8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032bc8` | `0x80032d94` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d94` | `0x80032ec8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032fb8` | `0x80033094` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80033094` | `0x800331e4` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331e4` | `0x800333c0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033570` | `0x8003375c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003375c` | `0x800337b0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800337b0` | `0x800337f8` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800337f8` | `0x800338cc` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338cc` | `0x800339ac` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800339ac` | `0x80033b64` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x8003457c` | `0x800345f8` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800345f8` | `0x800346e4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d48` | `0x80034db8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034db8` | `0x80034e18` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800351f4` | `0x80035248` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035410` | `0x8003567c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x8003567c` | `0x800359bc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800359bc` | `0x80035c6c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c6c` | `0x80035fa0` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035fa0` | `0x80036328` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036328` | `0x80036448` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036468` | `0x80036898` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x80036898` | `0x80036cdc` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d30` | `0x80036edc` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037350` | `0x80037514` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037ca4` | `0x80037f7c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038868` | `0x800388f8` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800388f8` | `0x800389c8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038ba0` | `0x80038bfc` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038dec` | `0x80039058` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039058` | `0x80039378` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039378` | `0x80039628` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039628` | `0x80039804` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039804` | `0x80039b4c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c98` | `0x8003b4fc` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b4fc` | `0x8003c738` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c85c` | `0x8003c978` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c988` | `0x8003c9b8` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c9b8` | `0x8003cf54` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf54` | `0x8003d264` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d264` | `0x8003d26c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d26c` | `0x8003d270` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d270` | `0x8003d454` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d54c` | `0x8003d794` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d794` | `0x8003ddf8` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ddf8` | `0x8003df14` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003df14` | `0x8003e12c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e12c` | `0x8003e16c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e16c` | `0x8003e1b4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e1b4` | `0x8003e204` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e204` | `0x8003e25c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e25c` | `0x8003e2bc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e2bc` | `0x8003e324` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e324` | `0x8003e394` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e394` | `0x8003e40c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e40c` | `0x8003e48c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e48c` | `0x8003e514` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e514` | `0x8003e5a4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e5a4` | `0x8003e63c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e63c` | `0x8003e6dc` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6dc` | `0x8003e784` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e784` | `0x8003e834` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e834` | `0x8003e8ec` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8ec` | `0x8003e9ac` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e9ac` | `0x8003ea74` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea74` | `0x8003eb44` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb44` | `0x8003ec1c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ec1c` | `0x8003ecfc` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ecfc` | `0x8003ede4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ede4` | `0x8003eed4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eed4` | `0x8003efcc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efcc` | `0x8003f0cc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0cc` | `0x8003f1d4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1d4` | `0x8003f2e4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2e4` | `0x8003f3fc` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f3fc` | `0x8003f51c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f51c` | `0x8003f644` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f644` | `0x8003f774` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f774` | `0x8003f8ac` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f8ac` | `0x8003f9ec` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9ec` | `0x8003fa64` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa64` | `0x8003fadc` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fadc` | `0x8003fb54` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb54` | `0x8003fbcc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fbcc` | `0x8003fc44` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc44` | `0x8003fcbc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fcbc` | `0x8003fd34` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd34` | `0x8003fdac` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fdac` | `0x8003fe24` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fe24` | `0x8003fe9c` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe9c` | `0x8003ff14` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ff14` | `0x8003ff8c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff8c` | `0x80040004` | 120 | `h_DUP13` | UNCONVERTED |
| `0x80040004` | `0x8004007c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8004007c` | `0x800400f4` | 120 | `h_DUP15` | UNCONVERTED |
| `0x800400f4` | `0x8004016c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8004016c` | `0x800401dc` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401dc` | `0x8004024c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8004024c` | `0x800402bc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800402bc` | `0x8004032c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8004032c` | `0x8004039c` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x8004039c` | `0x8004040c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8004040c` | `0x8004047c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8004047c` | `0x800404ec` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404ec` | `0x8004055c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8004055c` | `0x800405cc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405cc` | `0x8004063c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004063c` | `0x800406ac` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x800406ac` | `0x8004071c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004071c` | `0x8004078c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004078c` | `0x800407fc` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800407fc` | `0x8004086c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004086c` | `0x80040884` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040884` | `0x80040898` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x80040898` | `0x80040924` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040924` | `0x8004093c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004093c` | `0x80040950` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040950` | `0x800409d8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409d8` | `0x800409f0` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800409f0` | `0x80040a04` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040a04` | `0x80040a24` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040a24` | `0x80040a2c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a2c` | `0x80040a38` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a38` | `0x80040a3c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a3c` | `0x80040ac0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040ac0` | `0x80040b68` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b68` | `0x80040c9c` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c9c` | `0x80040d44` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d44` | `0x80040e3c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e3c` | `0x80040ed4` | 152 | `h_LT` | UNCONVERTED |
| `0x80040ed4` | `0x80040f6c` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f6c` | `0x80041000` | 148 | `h_SLT` | UNCONVERTED |
| `0x80041000` | `0x80041094` | 148 | `h_SGT` | UNCONVERTED |
| `0x80041094` | `0x80041118` | 132 | `h_EQ` | UNCONVERTED |
| `0x80041118` | `0x80041178` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041178` | `0x800411ec` | 116 | `h_AND` | UNCONVERTED |
| `0x800411ec` | `0x80041260` | 116 | `h_OR` | UNCONVERTED |
| `0x80041260` | `0x800412d4` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412d4` | `0x80041334` | 96 | `h_NOT` | UNCONVERTED |
| `0x80041334` | `0x80041420` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80041420` | `0x800415c0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800415c0` | `0x80041760` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041760` | `0x80041914` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041914` | `0x80041a14` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041a14` | `0x80041a48` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a48` | `0x80041d94` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d94` | `0x80042074` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042074` | `0x80042194` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80042194` | `0x800421d8` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421d8` | `0x8004221c` | 68 | `h_GAS` | UNCONVERTED |
| `0x8004221c` | `0x8004226c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x8004226c` | `0x800422bc` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800422bc` | `0x8004230c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x8004230c` | `0x8004235c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8004235c` | `0x800423ac` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800423ac` | `0x800423fc` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800423fc` | `0x8004244c` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x8004244c` | `0x8004249c` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x8004249c` | `0x800424ec` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424ec` | `0x8004253c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004253c` | `0x8004258c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x8004258c` | `0x800425dc` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425dc` | `0x8004262c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004262c` | `0x8004267c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x8004267c` | `0x800426cc` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426cc` | `0x80042764` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042764` | `0x80042850` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042850` | `0x80042894` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042894` | `0x80042ab0` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042ab0` | `0x80042c80` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c80` | `0x80042cc4` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042cc4` | `0x80042e90` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e90` | `0x80042e98` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e98` | `0x80042f58` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f58` | `0x8004304c` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x8004304c` | `0x80043090` | 68 | `h_PC` | UNCONVERTED |
| `0x80043090` | `0x80043318` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80043318` | `0x8004360c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004360c` | `0x80043920` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043920` | `0x80043c54` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c54` | `0x80043fa8` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043fa8` | `0x8004431c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x8004431c` | `0x800445c4` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800445c4` | `0x800448cc` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448cc` | `0x80044f38` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f38` | `0x800454e0` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454e0` | `0x80045a60` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a60` | `0x800462ec` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462ec` | `0x800463d8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463d8` | `0x800464a8` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800464a8` | `0x80046728` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046728` | `0x800470c0` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800470c0` | `0x800476a4` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800476a4` | `0x800476c0` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800476c0` | `0x80048be4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048be4` | `0x80048c30` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c30` | `0x80048dd4` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048dd4` | `0x80049b9c` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b9c` | `0x8004be48` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be48` | `0x8004cfc0` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cfc0` | `0x8004dc24` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dc24` | `0x8004ea2c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea2c` | `0x8004f690` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f690` | `0x8004ff48` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff48` | `0x8005083c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005083c` | `0x80050dd8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050dd8` | `0x80051484` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051484` | `0x800514a4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800514a4` | `0x80051b50` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b50` | `0x80051b70` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b70` | `0x800524a0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800524a0` | `0x800527ec` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527ec` | `0x8005295c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005295c` | `0x80052960` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052960` | `0x800529e8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529e8` | `0x80052bdc` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052bdc` | `0x80052c0c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052c0c` | `0x80052c20` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c20` | `0x80052c30` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c30` | `0x80052c60` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c60` | `0x80052e54` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e54` | `0x80052e84` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e84` | `0x80052e98` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e98` | `0x80052ea8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052ea8` | `0x80052ed8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052ed8` | `0x80052efc` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052efc` | `0x80052f2c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f2c` | `0x80053120` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80053120` | `0x80053150` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053150` | `0x80053164` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053164` | `0x80053174` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053174` | `0x800531a4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800531a4` | `0x80053398` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x80053398` | `0x800533c8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533c8` | `0x800533dc` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533dc` | `0x800533ec` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533ec` | `0x8005341c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005341c` | `0x80053610` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053610` | `0x80053640` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053640` | `0x80053654` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053654` | `0x80053664` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053664` | `0x80053694` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053694` | `0x80053694` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053694` | `0x800536b0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x8005383c` | `0x80053a70` | 564 | `stage_system_call_payload` | UNCONVERTED |
| `0x80053f70` | `0x800540a0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800540a0` | `0x800540fc` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800540fc` | `0x8005411c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005411c` | `0x80054258` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054428` | `0x80054434` | 12 | `requests_hash_verify` | TAIL |
