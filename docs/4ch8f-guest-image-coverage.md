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
not linked** (101 of 572 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80054440), 345152 bytes (`RegionMap.textSizeBytes = 0x54440`)

- symbols in `.text`: 909 (471 converted, 438 unconverted)
- covered by converted `_prog`s: 132052 bytes (38.26%)
- NOT covered: 213100 bytes (61.74%), 439 ranges

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
| `0x80019e20` | `0x80019eb4` | 148 | `rlp_field_to_u64_strict` | UNCONVERTED |
| `0x8001b40c` | `0x8001b728` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001baf0` | `0x8001bd68` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd68` | `0x8001c00c` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001c00c` | `0x8001cad0` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cde4` | `0x8001ce2c` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d4cc` | `0x8001d6b4` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d6b4` | `0x8001d710` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d710` | `0x8001d7dc` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7dc` | `0x8001d8b0` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d8b0` | `0x8001e840` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f114` | `0x8001f228` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f228` | `0x8001f65c` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x80020310` | `0x80020350` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x800205b0` | `0x800206f8` | 328 | `storage_writes_block_latest_value` | UNCONVERTED |
| `0x800206f8` | `0x80020728` | 48 | `exec_log_addr_to_bal_canonical` | UNCONVERTED |
| `0x80020c78` | `0x80020e08` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80021ffc` | `0x80022118` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80023a7c` | `0x80023a98` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023a98` | `0x80023b0c` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023b0c` | `0x80023b5c` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b5c` | `0x80023b88` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b88` | `0x80023c68` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c68` | `0x80023ce8` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023e58` | `0x80023f1c` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023f1c` | `0x80023f70` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f70` | `0x80023fa0` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x8002746c` | `0x80027af0` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028a0c` | `0x80028f28` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x8002aafc` | `0x8002ad98` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad98` | `0x8002add0` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ca2c` | `0x8002cf24` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cf24` | `0x8002db48` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db48` | `0x8002e118` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e118` | `0x8002fad8` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fad8` | `0x8002fafc` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fafc` | `0x8002fb18` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fb18` | `0x8002fddc` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fddc` | `0x8002fdec` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fdec` | `0x8002fe20` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fe20` | `0x8002fe38` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe38` | `0x8002fe48` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe48` | `0x8002fe7c` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe7c` | `0x8002fe84` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe84` | `0x8002ff30` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ff30` | `0x8002ff3c` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff3c` | `0x8002ff64` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff64` | `0x8002ffa4` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ffa4` | `0x8002ffd4` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffd4` | `0x8002ffd4` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffd4` | `0x8002ffec` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ffec` | `0x8002fff4` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fff4` | `0x80030000` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x80030000` | `0x80030018` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x80030018` | `0x80030030` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030030` | `0x80030044` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x80030044` | `0x80030064` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x80030064` | `0x80030078` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030078` | `0x800300a4` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x800300a4` | `0x800300ec` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300ec` | `0x800301cc` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x800301cc` | `0x8003027c` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x8003027c` | `0x8003029c` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x8003029c` | `0x80030310` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030310` | `0x80030320` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030320` | `0x8003032c` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x8003032c` | `0x80030410` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030410` | `0x80030438` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x80030438` | `0x8003044c` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x8003044c` | `0x8003044c` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x8003044c` | `0x8003044c` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x8003044c` | `0x8003046c` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x8003046c` | `0x8003049c` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x8003049c` | `0x800304c0` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x800304c0` | `0x800304e0` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304e0` | `0x800304e4` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304e4` | `0x80030584` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x80030584` | `0x80030594` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x80030594` | `0x800305a4` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800305a4` | `0x800306d4` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306d4` | `0x800306d4` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306d4` | `0x80030870` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030870` | `0x80030870` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030870` | `0x800308d0` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031688` | `0x800316b0` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800316b0` | `0x800318c0` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800319c0` | `0x80031a6c` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a6c` | `0x80031af0` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031b70` | `0x80031c28` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031c28` | `0x80031c9c` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c9c` | `0x80031e60` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e60` | `0x80031ed0` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031ed0` | `0x80031f48` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f48` | `0x800320f8` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320f8` | `0x80032174` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x80032174` | `0x800321c4` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800321c4` | `0x80032214` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x80032214` | `0x80032244` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x80032244` | `0x80032288` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032288` | `0x800322cc` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800322cc` | `0x8003237c` | 176 | `modexp_mul` | UNCONVERTED |
| `0x8003237c` | `0x800324d8` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324d8` | `0x800327d4` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327d4` | `0x800329b0` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800329b0` | `0x80032a5c` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a5c` | `0x80032bd4` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032bd4` | `0x80032da0` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032da0` | `0x80032ed4` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032fc4` | `0x800330a0` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800330a0` | `0x800331f0` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331f0` | `0x800333cc` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x8003357c` | `0x80033768` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80033768` | `0x800337bc` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800337bc` | `0x80033804` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x80033804` | `0x800338d8` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338d8` | `0x800339b8` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800339b8` | `0x80033b70` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034588` | `0x80034604` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x80034604` | `0x800346f0` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d54` | `0x80034dc4` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034dc4` | `0x80034e24` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80035200` | `0x80035254` | 84 | `bnq_sub` | UNCONVERTED |
| `0x8003541c` | `0x80035688` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035688` | `0x800359c8` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800359c8` | `0x80035c78` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c78` | `0x80035fac` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035fac` | `0x80036334` | 904 | `bng2_add` | UNCONVERTED |
| `0x80036334` | `0x80036454` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x80036474` | `0x800368a4` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800368a4` | `0x80036ce8` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d3c` | `0x80036ee8` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x8003735c` | `0x80037520` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037cb0` | `0x80037f88` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x80038874` | `0x80038904` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x80038904` | `0x800389d4` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038bac` | `0x80038c08` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038df8` | `0x80039064` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x80039064` | `0x80039384` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x80039384` | `0x80039634` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x80039634` | `0x80039810` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039810` | `0x80039b58` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039ca4` | `0x8003b508` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b508` | `0x8003c744` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c868` | `0x8003c984` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c994` | `0x8003c9c4` | 48 | `call_frame_forward_gas` | UNCONVERTED |
| `0x8003c9c4` | `0x8003cf60` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf60` | `0x8003d270` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d270` | `0x8003d278` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d278` | `0x8003d27c` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d27c` | `0x8003d460` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d558` | `0x8003d7a0` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d7a0` | `0x8003de04` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003de04` | `0x8003df20` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003df20` | `0x8003e138` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e138` | `0x8003e178` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e178` | `0x8003e1c0` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e1c0` | `0x8003e210` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e210` | `0x8003e268` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e268` | `0x8003e2c8` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e2c8` | `0x8003e330` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e330` | `0x8003e3a0` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e3a0` | `0x8003e418` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e418` | `0x8003e498` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e498` | `0x8003e520` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e520` | `0x8003e5b0` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e5b0` | `0x8003e648` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e648` | `0x8003e6e8` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6e8` | `0x8003e790` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e790` | `0x8003e840` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e840` | `0x8003e8f8` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8f8` | `0x8003e9b8` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e9b8` | `0x8003ea80` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea80` | `0x8003eb50` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb50` | `0x8003ec28` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ec28` | `0x8003ed08` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ed08` | `0x8003edf0` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003edf0` | `0x8003eee0` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eee0` | `0x8003efd8` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efd8` | `0x8003f0d8` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0d8` | `0x8003f1e0` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1e0` | `0x8003f2f0` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2f0` | `0x8003f408` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f408` | `0x8003f528` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f528` | `0x8003f650` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f650` | `0x8003f780` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f780` | `0x8003f8b8` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f8b8` | `0x8003f9f8` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9f8` | `0x8003fa70` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa70` | `0x8003fae8` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fae8` | `0x8003fb60` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb60` | `0x8003fbd8` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fbd8` | `0x8003fc50` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc50` | `0x8003fcc8` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fcc8` | `0x8003fd40` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd40` | `0x8003fdb8` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fdb8` | `0x8003fe30` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fe30` | `0x8003fea8` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fea8` | `0x8003ff20` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ff20` | `0x8003ff98` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff98` | `0x80040010` | 120 | `h_DUP13` | UNCONVERTED |
| `0x80040010` | `0x80040088` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040088` | `0x80040100` | 120 | `h_DUP15` | UNCONVERTED |
| `0x80040100` | `0x80040178` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040178` | `0x800401e8` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401e8` | `0x80040258` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x80040258` | `0x800402c8` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800402c8` | `0x80040338` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x80040338` | `0x800403a8` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x800403a8` | `0x80040418` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x80040418` | `0x80040488` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040488` | `0x800404f8` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404f8` | `0x80040568` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x80040568` | `0x800405d8` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405d8` | `0x80040648` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x80040648` | `0x800406b8` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x800406b8` | `0x80040728` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040728` | `0x80040798` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040798` | `0x80040808` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040808` | `0x80040878` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040878` | `0x80040890` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040890` | `0x800408a4` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800408a4` | `0x80040930` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040930` | `0x80040948` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040948` | `0x8004095c` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x8004095c` | `0x800409e4` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409e4` | `0x800409fc` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800409fc` | `0x80040a10` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040a10` | `0x80040a30` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040a30` | `0x80040a38` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a38` | `0x80040a44` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a44` | `0x80040a48` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a48` | `0x80040acc` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040acc` | `0x80040b74` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b74` | `0x80040ca8` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040ca8` | `0x80040d50` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d50` | `0x80040e48` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e48` | `0x80040ee0` | 152 | `h_LT` | UNCONVERTED |
| `0x80040ee0` | `0x80040f78` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f78` | `0x8004100c` | 148 | `h_SLT` | UNCONVERTED |
| `0x8004100c` | `0x800410a0` | 148 | `h_SGT` | UNCONVERTED |
| `0x800410a0` | `0x80041124` | 132 | `h_EQ` | UNCONVERTED |
| `0x80041124` | `0x80041184` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x80041184` | `0x800411f8` | 116 | `h_AND` | UNCONVERTED |
| `0x800411f8` | `0x8004126c` | 116 | `h_OR` | UNCONVERTED |
| `0x8004126c` | `0x800412e0` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412e0` | `0x80041340` | 96 | `h_NOT` | UNCONVERTED |
| `0x80041340` | `0x8004142c` | 236 | `h_BYTE` | UNCONVERTED |
| `0x8004142c` | `0x800415cc` | 416 | `h_SHL` | UNCONVERTED |
| `0x800415cc` | `0x8004176c` | 416 | `h_SHR` | UNCONVERTED |
| `0x8004176c` | `0x80041920` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041920` | `0x80041a20` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041a20` | `0x80041a54` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a54` | `0x80041da0` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041da0` | `0x80042080` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042080` | `0x800421a0` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800421a0` | `0x800421e4` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421e4` | `0x80042228` | 68 | `h_GAS` | UNCONVERTED |
| `0x80042228` | `0x80042278` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042278` | `0x800422c8` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800422c8` | `0x80042318` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80042318` | `0x80042368` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80042368` | `0x800423b8` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800423b8` | `0x80042408` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80042408` | `0x80042458` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80042458` | `0x800424a8` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800424a8` | `0x800424f8` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424f8` | `0x80042548` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80042548` | `0x80042598` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80042598` | `0x800425e8` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425e8` | `0x80042638` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042638` | `0x80042688` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042688` | `0x800426d8` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426d8` | `0x80042770` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042770` | `0x8004285c` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x8004285c` | `0x800428a0` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800428a0` | `0x80042abc` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042abc` | `0x80042c8c` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c8c` | `0x80042cd0` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042cd0` | `0x80042e9c` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e9c` | `0x80042ea4` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042ea4` | `0x80042f64` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f64` | `0x80043058` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80043058` | `0x8004309c` | 68 | `h_PC` | UNCONVERTED |
| `0x8004309c` | `0x80043324` | 648 | `h_KECCAK256` | UNCONVERTED |
| `0x80043324` | `0x80043618` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80043618` | `0x8004392c` | 788 | `h_LOG1` | UNCONVERTED |
| `0x8004392c` | `0x80043c60` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c60` | `0x80043fb4` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043fb4` | `0x80044328` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80044328` | `0x800445d0` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800445d0` | `0x800448d8` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448d8` | `0x80044f44` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f44` | `0x800454ec` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454ec` | `0x80045a6c` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a6c` | `0x800462f8` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462f8` | `0x800463e4` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463e4` | `0x800464b4` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800464b4` | `0x80046734` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x80046734` | `0x800470cc` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800470cc` | `0x800476b0` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800476b0` | `0x800476cc` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800476cc` | `0x80048bf0` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048bf0` | `0x80048c3c` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c3c` | `0x80048de0` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048de0` | `0x80049ba8` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049ba8` | `0x8004be54` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be54` | `0x8004cfcc` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cfcc` | `0x8004dc30` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dc30` | `0x8004ea38` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea38` | `0x8004f69c` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f69c` | `0x8004ff54` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff54` | `0x80050848` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050848` | `0x80050de4` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050de4` | `0x80051490` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051490` | `0x800514b0` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800514b0` | `0x80051b5c` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b5c` | `0x80051b7c` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b7c` | `0x800524ac` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800524ac` | `0x800527f8` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527f8` | `0x80052968` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052968` | `0x8005296c` | 4 | `h_invalid` | UNCONVERTED |
| `0x8005296c` | `0x800529f4` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529f4` | `0x80052be8` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052be8` | `0x80052c18` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052c18` | `0x80052c2c` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c2c` | `0x80052c3c` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c3c` | `0x80052c6c` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c6c` | `0x80052e60` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e60` | `0x80052e90` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e90` | `0x80052ea4` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052ea4` | `0x80052eb4` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052eb4` | `0x80052ee4` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052ee4` | `0x80052f08` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052f08` | `0x80052f38` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f38` | `0x8005312c` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x8005312c` | `0x8005315c` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x8005315c` | `0x80053170` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053170` | `0x80053180` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053180` | `0x800531b0` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800531b0` | `0x800533a4` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800533a4` | `0x800533d4` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533d4` | `0x800533e8` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533e8` | `0x800533f8` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533f8` | `0x80053428` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053428` | `0x8005361c` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x8005361c` | `0x8005364c` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x8005364c` | `0x80053660` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053660` | `0x80053670` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053670` | `0x800536a0` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800536a0` | `0x800536a0` | 0 | `.exit_label` | UNCONVERTED |
| `0x800536a0` | `0x800536bc` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053f7c` | `0x800540ac` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800540ac` | `0x80054108` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054108` | `0x80054128` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80054128` | `0x80054264` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x80054434` | `0x80054440` | 12 | `requests_hash_verify` | TAIL |
