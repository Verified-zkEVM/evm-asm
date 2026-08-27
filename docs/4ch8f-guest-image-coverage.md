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
not linked** (87 of 562 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80054444), 345156 bytes (`RegionMap.textSizeBytes = 0x54444`)

- symbols in `.text`: 909 (475 converted, 434 unconverted)
- covered by converted `_prog`s: 132628 bytes (38.43%)
- NOT covered: 212528 bytes (61.57%), 435 ranges

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
| `0x8000999c` | `0x80009b60` | 452 | `mpt_indexed_trie_root_one_leaf` | UNCONVERTED |
| `0x80009b60` | `0x80009bcc` | 108 | `rlp_prefix_to_buffer` | UNCONVERTED |
| `0x8000a488` | `0x8000a688` | 512 | `mpt_indexed_sort_changes` | UNCONVERTED |
| `0x8000a688` | `0x8000a7c8` | 320 | `mpt_indexed_leaf_ref` | UNCONVERTED |
| `0x8000a7c8` | `0x8000aa84` | 700 | `mpt_indexed_build_subtree` | UNCONVERTED |
| `0x8000aa84` | `0x8000ab74` | 240 | `mpt_indexed_trie_root_bounded` | UNCONVERTED |
| `0x8000ab74` | `0x8000ace4` | 368 | `mpt_indexed_trie_root_bounded_from_values` | UNCONVERTED |
| `0x8000e5ec` | `0x8000f908` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fd38` | `0x8000ff18` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000ff18` | `0x8000fffc` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x8000fffc` | `0x800100d8` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x800100d8` | `0x8001016c` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x8001016c` | `0x80010228` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x80010228` | `0x800102d8` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x800102d8` | `0x800103bc` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x800103bc` | `0x800103f8` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103f8` | `0x80010528` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x80010528` | `0x8001064c` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x8001064c` | `0x800106fc` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x800106fc` | `0x80010878` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x80010878` | `0x80010950` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010950` | `0x80010ae0` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010ae0` | `0x80010c7c` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c7c` | `0x80010d2c` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010d2c` | `0x80010d94` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d94` | `0x80010e30` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010e30` | `0x80011464` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011464` | `0x8001174c` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x8001174c` | `0x80011aa4` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011aa4` | `0x80011f80` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f80` | `0x80012224` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80012224` | `0x80012340` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80012340` | `0x800125f8` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125f8` | `0x80012818` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x80012818` | `0x80012bb0` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012bb0` | `0x80012cc4` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012cc4` | `0x80012ce4` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012ce4` | `0x80012f6c` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f6c` | `0x80013050` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80013050` | `0x800130f8` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130f8` | `0x8001382c` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x8001382c` | `0x80013e64` | 1592 | `block_state_root` | UNCONVERTED |
| `0x800141a0` | `0x800141b4` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x800141b4` | `0x800141c0` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800141c0` | `0x80014210` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80014210` | `0x80014230` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80014230` | `0x80014294` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014294` | `0x8001453c` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x8001453c` | `0x80014790` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014790` | `0x80014944` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015544` | `0x8001573c` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a5c` | `0x80015c8c` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x8001607c` | `0x80018b88` | 11020 | `block_verdict` | UNCONVERTED |
| `0x80018b88` | `0x8001991c` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x8001991c` | `0x80019b38` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x8001b40c` | `0x8001b728` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001baf0` | `0x8001bd68` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd68` | `0x8001c00c` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001c00c` | `0x8001cad0` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cde4` | `0x8001ce2c` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d4d0` | `0x8001d6b8` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d6b8` | `0x8001d714` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d714` | `0x8001d7e0` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7e0` | `0x8001d8b4` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d8b4` | `0x8001e844` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f118` | `0x8001f22c` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f22c` | `0x8001f660` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x80020314` | `0x80020354` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020c7c` | `0x80020e0c` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80022000` | `0x8002211c` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80023a80` | `0x80023a9c` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a9c` | `0x80023b10` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023b10` | `0x80023b60` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b60` | `0x80023b8c` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b8c` | `0x80023c6c` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c6c` | `0x80023cec` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023e5c` | `0x80023f20` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023f20` | `0x80023f74` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f74` | `0x80023fa4` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80027470` | `0x80027af4` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028a10` | `0x80028f2c` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x8002ab00` | `0x8002ad9c` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad9c` | `0x8002add4` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ca30` | `0x8002cf28` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cf28` | `0x8002db4c` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db4c` | `0x8002e11c` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e11c` | `0x8002fadc` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fadc` | `0x8002fb00` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fb00` | `0x8002fb1c` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fb1c` | `0x8002fde0` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fde0` | `0x8002fdf0` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fdf0` | `0x8002fe24` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fe24` | `0x8002fe3c` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe3c` | `0x8002fe4c` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe4c` | `0x8002fe80` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe80` | `0x8002fe88` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe88` | `0x8002ff34` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ff34` | `0x8002ff40` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff40` | `0x8002ff68` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff68` | `0x8002ffa8` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ffa8` | `0x8002ffd8` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffd8` | `0x8002ffd8` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffd8` | `0x8002fff0` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fff0` | `0x8002fff8` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fff8` | `0x80030004` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x80030004` | `0x8003001c` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8003001c` | `0x80030034` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030034` | `0x80030048` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030048` | `0x80030068` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030068` | `0x8003007c` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x8003007c` | `0x800300a8` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x800300a8` | `0x800300f0` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300f0` | `0x800301d0` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x800301d0` | `0x80030280` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030280` | `0x800302a0` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x800302a0` | `0x80030314` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030314` | `0x80030324` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030324` | `0x80030330` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x80030330` | `0x80030414` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030414` | `0x8003043c` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x8003043c` | `0x80030450` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030450` | `0x80030450` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030450` | `0x80030450` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030450` | `0x80030470` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030470` | `0x800304a0` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x800304a0` | `0x800304c4` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x800304c4` | `0x800304e4` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304e4` | `0x800304e8` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304e8` | `0x80030588` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030588` | `0x80030598` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030598` | `0x800305a8` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800305a8` | `0x800306d8` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306d8` | `0x800306d8` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306d8` | `0x80030874` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030874` | `0x80030874` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030874` | `0x800308d4` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x8003168c` | `0x800316b4` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800316b4` | `0x800318c4` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800319c4` | `0x80031a70` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a70` | `0x80031af4` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031b74` | `0x80031c2c` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031c2c` | `0x80031ca0` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031ca0` | `0x80031e64` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e64` | `0x80031ed4` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031ed4` | `0x80031f4c` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f4c` | `0x800320fc` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320fc` | `0x80032178` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032178` | `0x800321c8` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800321c8` | `0x80032218` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80032218` | `0x80032248` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032248` | `0x8003228c` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x8003228c` | `0x800322d0` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800322d0` | `0x80032380` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032380` | `0x800324dc` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324dc` | `0x800327d8` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327d8` | `0x800329b4` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800329b4` | `0x80032a60` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a60` | `0x80032bd8` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032bd8` | `0x80032da4` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032da4` | `0x80032ed8` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032fc8` | `0x800330a4` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800330a4` | `0x800331f4` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331f4` | `0x800333d0` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033580` | `0x8003376c` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x8003376c` | `0x800337c0` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800337c0` | `0x80033808` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033808` | `0x800338dc` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338dc` | `0x800339bc` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800339bc` | `0x80033b74` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x8003458c` | `0x80034608` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034608` | `0x800346f4` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d58` | `0x80034dc8` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034dc8` | `0x80034e28` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80035204` | `0x80035258` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035420` | `0x8003568c` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x8003568c` | `0x800359cc` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800359cc` | `0x80035c7c` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c7c` | `0x80035fb0` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035fb0` | `0x80036338` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036338` | `0x80036458` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036478` | `0x800368a8` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800368a8` | `0x80036cec` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d40` | `0x80036eec` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037360` | `0x80037524` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037cb4` | `0x80037f8c` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038878` | `0x80038908` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038908` | `0x800389d8` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038bb0` | `0x80038c0c` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038dfc` | `0x80039068` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039068` | `0x80039388` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039388` | `0x80039638` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039638` | `0x80039814` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039814` | `0x80039b5c` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039ca8` | `0x8003b50c` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b50c` | `0x8003c748` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c86c` | `0x8003c988` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c9c8` | `0x8003cf64` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf64` | `0x8003d274` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d274` | `0x8003d27c` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d27c` | `0x8003d280` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d280` | `0x8003d464` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d55c` | `0x8003d7a4` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d7a4` | `0x8003de08` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003de08` | `0x8003df24` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003df24` | `0x8003e13c` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e13c` | `0x8003e17c` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e17c` | `0x8003e1c4` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e1c4` | `0x8003e214` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e214` | `0x8003e26c` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e26c` | `0x8003e2cc` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e2cc` | `0x8003e334` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e334` | `0x8003e3a4` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e3a4` | `0x8003e41c` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e41c` | `0x8003e49c` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e49c` | `0x8003e524` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e524` | `0x8003e5b4` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e5b4` | `0x8003e64c` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e64c` | `0x8003e6ec` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6ec` | `0x8003e794` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e794` | `0x8003e844` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e844` | `0x8003e8fc` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8fc` | `0x8003e9bc` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e9bc` | `0x8003ea84` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea84` | `0x8003eb54` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb54` | `0x8003ec2c` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ec2c` | `0x8003ed0c` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ed0c` | `0x8003edf4` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003edf4` | `0x8003eee4` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eee4` | `0x8003efdc` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efdc` | `0x8003f0dc` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0dc` | `0x8003f1e4` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1e4` | `0x8003f2f4` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2f4` | `0x8003f40c` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f40c` | `0x8003f52c` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f52c` | `0x8003f654` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f654` | `0x8003f784` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f784` | `0x8003f8bc` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f8bc` | `0x8003f9fc` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9fc` | `0x8003fa74` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa74` | `0x8003faec` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003faec` | `0x8003fb64` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb64` | `0x8003fbdc` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fbdc` | `0x8003fc54` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc54` | `0x8003fccc` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fccc` | `0x8003fd44` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd44` | `0x8003fdbc` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fdbc` | `0x8003fe34` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fe34` | `0x8003feac` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003feac` | `0x8003ff24` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ff24` | `0x8003ff9c` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff9c` | `0x80040014` | 120 | `h_DUP13` | UNCONVERTED |
| `0x80040014` | `0x8004008c` | 120 | `h_DUP14` | UNCONVERTED |
| `0x8004008c` | `0x80040104` | 120 | `h_DUP15` | UNCONVERTED |
| `0x80040104` | `0x8004017c` | 120 | `h_DUP16` | UNCONVERTED |
| `0x8004017c` | `0x800401ec` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401ec` | `0x8004025c` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x8004025c` | `0x800402cc` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800402cc` | `0x8004033c` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x8004033c` | `0x800403ac` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x800403ac` | `0x8004041c` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x8004041c` | `0x8004048c` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x8004048c` | `0x800404fc` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404fc` | `0x8004056c` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x8004056c` | `0x800405dc` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405dc` | `0x8004064c` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x8004064c` | `0x800406bc` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x800406bc` | `0x8004072c` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x8004072c` | `0x8004079c` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x8004079c` | `0x8004080c` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x8004080c` | `0x8004087c` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x8004087c` | `0x80040894` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040894` | `0x800408a8` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800408a8` | `0x80040934` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040934` | `0x8004094c` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x8004094c` | `0x80040960` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040960` | `0x800409e8` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409e8` | `0x80040a00` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040a00` | `0x80040a14` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040a14` | `0x80040a34` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040a34` | `0x80040a3c` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a3c` | `0x80040a48` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a48` | `0x80040a4c` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a4c` | `0x80040ad0` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040ad0` | `0x80040b78` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b78` | `0x80040cac` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040cac` | `0x80040d54` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d54` | `0x80040e4c` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e4c` | `0x80040ee4` | 152 | `h_LT` | UNCONVERTED |
| `0x80040ee4` | `0x80040f7c` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f7c` | `0x80041010` | 148 | `h_SLT` | UNCONVERTED |
| `0x80041010` | `0x800410a4` | 148 | `h_SGT` | UNCONVERTED |
| `0x800410a4` | `0x80041128` | 132 | `h_EQ` | UNCONVERTED |
| `0x80041128` | `0x80041188` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041188` | `0x800411fc` | 116 | `h_AND` | UNCONVERTED |
| `0x800411fc` | `0x80041270` | 116 | `h_OR` | UNCONVERTED |
| `0x80041270` | `0x800412e4` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412e4` | `0x80041344` | 96 | `h_NOT` | UNCONVERTED |
| `0x80041344` | `0x80041430` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80041430` | `0x800415d0` | 416 | `h_SHL` | UNCONVERTED |
| `0x800415d0` | `0x80041770` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041770` | `0x80041924` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041924` | `0x80041a24` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041a24` | `0x80041a58` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a58` | `0x80041da4` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041da4` | `0x80042084` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042084` | `0x800421a4` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800421a4` | `0x800421e8` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421e8` | `0x8004222c` | 68 | `h_GAS` | UNCONVERTED |
| `0x8004222c` | `0x8004227c` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x8004227c` | `0x800422cc` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800422cc` | `0x8004231c` | 80 | `h_CALLER` | UNCONVERTED |
| `0x8004231c` | `0x8004236c` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x8004236c` | `0x800423bc` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800423bc` | `0x8004240c` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x8004240c` | `0x8004245c` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x8004245c` | `0x800424ac` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800424ac` | `0x800424fc` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424fc` | `0x8004254c` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x8004254c` | `0x8004259c` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x8004259c` | `0x800425ec` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425ec` | `0x8004263c` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x8004263c` | `0x8004268c` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x8004268c` | `0x800426dc` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426dc` | `0x80042774` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042774` | `0x80042860` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042860` | `0x800428a4` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800428a4` | `0x80042ac0` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042ac0` | `0x80042c90` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c90` | `0x80042cd4` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042cd4` | `0x80042ea0` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042ea0` | `0x80042ea8` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042ea8` | `0x80042f68` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f68` | `0x8004305c` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x8004305c` | `0x800430a0` | 68 | `h_PC` | UNCONVERTED |
| `0x800430a0` | `0x80043328` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80043328` | `0x8004361c` | 756 | `h_LOG0` | UNCONVERTED |
| `0x8004361c` | `0x80043930` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043930` | `0x80043c64` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c64` | `0x80043fb8` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043fb8` | `0x8004432c` | 884 | `h_LOG4` | UNCONVERTED |
| `0x8004432c` | `0x800445d4` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800445d4` | `0x800448dc` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448dc` | `0x80044f48` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f48` | `0x800454f0` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454f0` | `0x80045a70` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a70` | `0x800462fc` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462fc` | `0x800463e8` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463e8` | `0x800464b8` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800464b8` | `0x80046738` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046738` | `0x800470d0` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800470d0` | `0x800476b4` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800476b4` | `0x800476d0` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800476d0` | `0x80048bf4` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048bf4` | `0x80048c40` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c40` | `0x80048de4` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048de4` | `0x80049bac` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049bac` | `0x8004be58` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be58` | `0x8004cfd0` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cfd0` | `0x8004dc34` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dc34` | `0x8004ea3c` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea3c` | `0x8004f6a0` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f6a0` | `0x8004ff58` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff58` | `0x8005084c` | 2292 | `h_DIV` | UNCONVERTED |
| `0x8005084c` | `0x80050de8` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050de8` | `0x80051494` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051494` | `0x800514b4` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800514b4` | `0x80051b60` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b60` | `0x80051b80` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b80` | `0x800524b0` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800524b0` | `0x800527fc` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527fc` | `0x8005296c` | 368 | `h_STOP` | UNCONVERTED |
| `0x8005296c` | `0x80052970` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052970` | `0x800529f8` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529f8` | `0x80052bec` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052bec` | `0x80052c1c` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052c1c` | `0x80052c30` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c30` | `0x80052c40` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c40` | `0x80052c70` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c70` | `0x80052e64` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e64` | `0x80052e94` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e94` | `0x80052ea8` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052ea8` | `0x80052eb8` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052eb8` | `0x80052ee8` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052ee8` | `0x80052f0c` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052f0c` | `0x80052f3c` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f3c` | `0x80053130` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80053130` | `0x80053160` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053160` | `0x80053174` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053174` | `0x80053184` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053184` | `0x800531b4` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800531b4` | `0x800533a8` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800533a8` | `0x800533d8` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533d8` | `0x800533ec` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533ec` | `0x800533fc` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533fc` | `0x8005342c` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x8005342c` | `0x80053620` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053620` | `0x80053650` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053650` | `0x80053664` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053664` | `0x80053674` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053674` | `0x800536a4` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800536a4` | `0x800536a4` | 0 | `.exit_label` | UNCONVERTED |
| `0x800536a4` | `0x800536c0` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053f80` | `0x800540b0` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800540b0` | `0x8005410c` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x8005410c` | `0x8005412c` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x8005412c` | `0x80054268` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054438` | `0x80054444` | 12 | `requests_hash_verify` | TAIL |
