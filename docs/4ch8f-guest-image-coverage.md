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
not linked** (85 of 561 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x800543e8), 345064 bytes (`RegionMap.textSizeBytes = 0x543e8`)

- symbols in `.text`: 909 (476 converted, 433 unconverted)
- covered by converted `_prog`s: 133248 bytes (38.62%)
- NOT covered: 211816 bytes (61.38%), 434 ranges

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
| `0x8000e5f0` | `0x8000f90c` | 4892 | `map_account_apply_post_fields` | UNCONVERTED |
| `0x8000fd3c` | `0x8000ff1c` | 480 | `mpt_bounded_sort_changes` | UNCONVERTED |
| `0x8000ff1c` | `0x80010000` | 228 | `mpt_bounded_prepare_changes` | UNCONVERTED |
| `0x80010000` | `0x800100dc` | 220 | `mpt_bounded_capture_branch_refs` | UNCONVERTED |
| `0x800100dc` | `0x80010170` | 148 | `mpt_bounded_resolve_witness` | UNCONVERTED |
| `0x80010170` | `0x8001022c` | 188 | `mpt_bounded_classify_node` | UNCONVERTED |
| `0x8001022c` | `0x800102dc` | 176 | `mpt_bounded_open_root_frame` | UNCONVERTED |
| `0x800102dc` | `0x800103c0` | 228 | `mpt_bounded_open_child_frame` | UNCONVERTED |
| `0x800103c0` | `0x800103fc` | 60 | `mpt_bounded_invalidate_constructed_cache` | UNCONVERTED |
| `0x800103fc` | `0x8001052c` | 304 | `mpt_bounded_snapshot_constructed_child` | UNCONVERTED |
| `0x8001052c` | `0x80010650` | 292 | `mpt_bounded_open_constructed_child_frame` | UNCONVERTED |
| `0x80010650` | `0x80010700` | 176 | `mpt_bounded_node_ref` | UNCONVERTED |
| `0x80010700` | `0x8001087c` | 380 | `mpt_bounded_encode_branch` | UNCONVERTED |
| `0x8001087c` | `0x80010954` | 216 | `mpt_bounded_encode_leaf_ref` | UNCONVERTED |
| `0x80010954` | `0x80010ae4` | 400 | `mpt_bounded_decode_extension` | UNCONVERTED |
| `0x80010ae4` | `0x80010c80` | 412 | `mpt_bounded_decode_leaf` | UNCONVERTED |
| `0x80010c80` | `0x80010d30` | 176 | `mpt_bounded_decode_frame_payload` | UNCONVERTED |
| `0x80010d30` | `0x80010d98` | 104 | `mpt_bounded_frame_path_match` | UNCONVERTED |
| `0x80010d98` | `0x80010e34` | 156 | `mpt_bounded_interval_old_prefix` | UNCONVERTED |
| `0x80010e34` | `0x80011468` | 1588 | `mpt_bounded_split_leaf_group` | UNCONVERTED |
| `0x80011468` | `0x80011750` | 744 | `mpt_bounded_split_leaf` | UNCONVERTED |
| `0x80011750` | `0x80011aa8` | 856 | `mpt_bounded_split_extension` | UNCONVERTED |
| `0x80011aa8` | `0x80011f84` | 1244 | `mpt_bounded_split_extension_group` | UNCONVERTED |
| `0x80011f84` | `0x80012228` | 676 | `mpt_bounded_collapse_branch_leaf` | UNCONVERTED |
| `0x80012228` | `0x80012344` | 284 | `mpt_bounded_rebuild_exact_leaf` | UNCONVERTED |
| `0x80012344` | `0x800125fc` | 696 | `mpt_bounded_build_missing_subtree` | UNCONVERTED |
| `0x800125fc` | `0x8001281c` | 544 | `mpt_bounded_rebuild_subtree` | UNCONVERTED |
| `0x8001281c` | `0x80012bb4` | 920 | `mpt_bounded_extension_merge_probe` | UNCONVERTED |
| `0x80012bb4` | `0x80012cc8` | 276 | `mpt_bounded_encode_extension` | UNCONVERTED |
| `0x80012cc8` | `0x80012ce8` | 32 | `mpt_bounded_state_root` | UNCONVERTED |
| `0x80012ce8` | `0x80012f70` | 648 | `mpt_bounded_storage_root` | UNCONVERTED |
| `0x80012f70` | `0x80013054` | 228 | `mpt_bounded_partition_frame` | UNCONVERTED |
| `0x80013054` | `0x800130fc` | 168 | `block_state_root_pre_accounts` | UNCONVERTED |
| `0x800130fc` | `0x80013830` | 1844 | `execution_map_state_changes` | UNCONVERTED |
| `0x80013830` | `0x80013e68` | 1592 | `block_state_root` | UNCONVERTED |
| `0x800141a4` | `0x800141b8` | 20 | `receipt_records_init` | UNCONVERTED |
| `0x800141b8` | `0x800141c4` | 12 | `receipt_records_clear` | UNCONVERTED |
| `0x800141c4` | `0x80014214` | 80 | `receipt_records_append` | UNCONVERTED |
| `0x80014214` | `0x80014234` | 32 | `receipt_records_append_runtime_result` | UNCONVERTED |
| `0x80014234` | `0x80014298` | 100 | `receipt_record_nth` | UNCONVERTED |
| `0x80014298` | `0x80014540` | 680 | `block_receipt_records_materialize` | UNCONVERTED |
| `0x80014540` | `0x80014794` | 596 | `block_log_window_snapshot` | UNCONVERTED |
| `0x80014794` | `0x80014948` | 436 | `block_receipt_logs_materialize` | UNCONVERTED |
| `0x80015548` | `0x80015740` | 504 | `receipt_records_encode_no_logs` | UNCONVERTED |
| `0x80015a60` | `0x80015c90` | 560 | `block_validate_receipts_consensus_list` | UNCONVERTED |
| `0x80016080` | `0x80018b8c` | 11020 | `block_verdict` | UNCONVERTED |
| `0x80018b8c` | `0x80019920` | 3476 | `block_verdict_mtx_oog_materialize` | UNCONVERTED |
| `0x80019920` | `0x80019b3c` | 540 | `block_verdict_withdrawal_nonstorage_effects` | UNCONVERTED |
| `0x8001b410` | `0x8001b72c` | 796 | `account_state_delegation_code_resolve` | UNCONVERTED |
| `0x8001baf4` | `0x8001bd6c` | 632 | `stage_runtime_payload` | UNCONVERTED |
| `0x8001bd6c` | `0x8001c010` | 676 | `stage_creation_runtime_payload` | UNCONVERTED |
| `0x8001c010` | `0x8001cad4` | 2756 | `block_verdict_creation_runtime` | UNCONVERTED |
| `0x8001cde8` | `0x8001ce30` | 72 | `bytecode_is_self_contained` | UNCONVERTED |
| `0x8001d4d4` | `0x8001d6bc` | 488 | `dtrc_materialize_deferred_delegation` | UNCONVERTED |
| `0x8001d6bc` | `0x8001d718` | 92 | `dtrc_charge_deferred_delegation` | UNCONVERTED |
| `0x8001d718` | `0x8001d7e4` | 204 | `dispatcher_capture_body_state` | UNCONVERTED |
| `0x8001d7e4` | `0x8001d8b8` | 212 | `dispatcher_restore_body_state` | UNCONVERTED |
| `0x8001d8b8` | `0x8001e848` | 3984 | `dispatch_tx_runtime_code` | UNCONVERTED |
| `0x8001f11c` | `0x8001f230` | 276 | `evm_storage_access_seed_key` | UNCONVERTED |
| `0x8001f230` | `0x8001f664` | 1076 | `seed_tx_access_list` | UNCONVERTED |
| `0x80020318` | `0x80020358` | 64 | `bal_addr_to_exec_log_key` | UNCONVERTED |
| `0x80020c80` | `0x80020e10` | 400 | `destroy_storage` | UNCONVERTED |
| `0x80022004` | `0x80022120` | 284 | `account_agreement_mutation_checkpoint` | UNCONVERTED |
| `0x80023a84` | `0x80023aa0` | 28 | `keccak_init` | UNCONVERTED |
| `0x80023aa0` | `0x80023b14` | 116 | `keccak_absorb` | UNCONVERTED |
| `0x80023b14` | `0x80023b64` | 80 | `keccak_final` | UNCONVERTED |
| `0x80023b64` | `0x80023b90` | 44 | `bal_rlp_scalar_len` | UNCONVERTED |
| `0x80023b90` | `0x80023c70` | 224 | `bal_rlp_emit_scalar` | UNCONVERTED |
| `0x80023c70` | `0x80023cf0` | 128 | `bal_rlp_emit_address` | UNCONVERTED |
| `0x80023e60` | `0x80023f24` | 196 | `bal_rlp_emit_list_header` | UNCONVERTED |
| `0x80023f24` | `0x80023f78` | 84 | `bal_rlp_scalar_rlp_len` | UNCONVERTED |
| `0x80023f78` | `0x80023fa8` | 48 | `bal_rlp_list_header_len` | UNCONVERTED |
| `0x80027474` | `0x80027af8` | 1668 | `tx_gas_bal_post_verify` | UNCONVERTED |
| `0x80028a14` | `0x80028f30` | 1308 | `tx_gas_bal_post_verify_runtime` | UNCONVERTED |
| `0x8002aaa4` | `0x8002ad40` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ad40` | `0x8002ad78` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002c9d4` | `0x8002cecc` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cecc` | `0x8002daf0` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002daf0` | `0x8002e0c0` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e0c0` | `0x8002fa80` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fa80` | `0x8002faa4` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002faa4` | `0x8002fac0` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fac0` | `0x8002fd84` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fd84` | `0x8002fd94` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fd94` | `0x8002fdc8` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fdc8` | `0x8002fde0` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fde0` | `0x8002fdf0` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fdf0` | `0x8002fe24` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe24` | `0x8002fe2c` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe2c` | `0x8002fed8` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002fed8` | `0x8002fee4` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002fee4` | `0x8002ff0c` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff0c` | `0x8002ff4c` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ff4c` | `0x8002ff7c` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ff7c` | `0x8002ff7c` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ff7c` | `0x8002ff94` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002ff94` | `0x8002ff9c` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002ff9c` | `0x8002ffa8` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x8002ffa8` | `0x8002ffc0` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x8002ffc0` | `0x8002ffd8` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x8002ffd8` | `0x8002ffec` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8002ffec` | `0x8003000c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8003000c` | `0x80030020` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030020` | `0x8003004c` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x8003004c` | `0x80030094` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x80030094` | `0x80030174` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x80030174` | `0x80030224` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030224` | `0x80030244` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x80030244` | `0x800302b8` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x800302b8` | `0x800302c8` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x800302c8` | `0x800302d4` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x800302d4` | `0x800303b8` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x800303b8` | `0x800303e0` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x800303e0` | `0x800303f4` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x800303f4` | `0x800303f4` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x800303f4` | `0x800303f4` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x800303f4` | `0x80030414` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030414` | `0x80030444` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x80030444` | `0x80030468` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x80030468` | `0x80030488` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x80030488` | `0x8003048c` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x8003048c` | `0x8003052c` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8003052c` | `0x8003053c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8003053c` | `0x8003054c` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x8003054c` | `0x8003067c` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x8003067c` | `0x8003067c` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x8003067c` | `0x800307d8` | 348 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030818` | `0x80030818` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030818` | `0x80030878` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031630` | `0x80031658` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x80031658` | `0x80031868` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x80031968` | `0x80031a14` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a14` | `0x80031a98` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031b18` | `0x80031bd0` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031bd0` | `0x80031c44` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031c44` | `0x80031e08` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e08` | `0x80031e78` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031e78` | `0x80031ef0` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031ef0` | `0x800320a0` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x800320a0` | `0x8003211c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003211c` | `0x8003216c` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x8003216c` | `0x800321bc` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x800321bc` | `0x800321ec` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x800321ec` | `0x80032230` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032230` | `0x80032274` | 68 | `modexp_sub` | UNCONVERTED |
| `0x80032274` | `0x80032324` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032324` | `0x80032480` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x80032480` | `0x8003277c` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x8003277c` | `0x80032958` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x80032958` | `0x80032a04` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a04` | `0x80032b7c` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032b7c` | `0x80032d48` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032d48` | `0x80032e7c` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032f6c` | `0x80033048` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x80033048` | `0x80033198` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x80033198` | `0x80033374` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033524` | `0x80033710` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80033710` | `0x80033764` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x80033764` | `0x800337ac` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x800337ac` | `0x80033880` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x80033880` | `0x80033960` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x80033960` | `0x80033b18` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034530` | `0x800345ac` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x800345ac` | `0x80034698` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034cfc` | `0x80034d6c` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034d6c` | `0x80034dcc` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x800351a8` | `0x800351fc` | 84 | `bnq_sub` | UNCONVERTED |
| `0x800353c4` | `0x80035630` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035630` | `0x80035970` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x80035970` | `0x80035c20` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c20` | `0x80035f54` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035f54` | `0x800362dc` | 904 | `bng2_add` | UNCONVERTED |
| `0x800362dc` | `0x800363fc` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x8003641c` | `0x8003684c` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x8003684c` | `0x80036c90` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036ce4` | `0x80036e90` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037304` | `0x800374c8` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037c58` | `0x80037f30` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003881c` | `0x800388ac` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x800388ac` | `0x8003897c` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038b54` | `0x80038bb0` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038da0` | `0x8003900c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003900c` | `0x8003932c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003932c` | `0x800395dc` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x800395dc` | `0x800397b8` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x800397b8` | `0x80039b00` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039c4c` | `0x8003b4b0` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b4b0` | `0x8003c6ec` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c810` | `0x8003c92c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c96c` | `0x8003cf08` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf08` | `0x8003d218` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d218` | `0x8003d220` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d220` | `0x8003d224` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d224` | `0x8003d408` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d500` | `0x8003d748` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d748` | `0x8003ddac` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003ddac` | `0x8003dec8` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003dec8` | `0x8003e0e0` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e0e0` | `0x8003e120` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e120` | `0x8003e168` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e168` | `0x8003e1b8` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e1b8` | `0x8003e210` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e210` | `0x8003e270` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e270` | `0x8003e2d8` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e2d8` | `0x8003e348` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e348` | `0x8003e3c0` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e3c0` | `0x8003e440` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e440` | `0x8003e4c8` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e4c8` | `0x8003e558` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e558` | `0x8003e5f0` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e5f0` | `0x8003e690` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e690` | `0x8003e738` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e738` | `0x8003e7e8` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e7e8` | `0x8003e8a0` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e8a0` | `0x8003e960` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e960` | `0x8003ea28` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea28` | `0x8003eaf8` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eaf8` | `0x8003ebd0` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ebd0` | `0x8003ecb0` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ecb0` | `0x8003ed98` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003ed98` | `0x8003ee88` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003ee88` | `0x8003ef80` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003ef80` | `0x8003f080` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f080` | `0x8003f188` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f188` | `0x8003f298` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f298` | `0x8003f3b0` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f3b0` | `0x8003f4d0` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f4d0` | `0x8003f5f8` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f5f8` | `0x8003f728` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f728` | `0x8003f860` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f860` | `0x8003f9a0` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003f9a0` | `0x8003fa18` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa18` | `0x8003fa90` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003fa90` | `0x8003fb08` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb08` | `0x8003fb80` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fb80` | `0x8003fbf8` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fbf8` | `0x8003fc70` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fc70` | `0x8003fce8` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fce8` | `0x8003fd60` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fd60` | `0x8003fdd8` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fdd8` | `0x8003fe50` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003fe50` | `0x8003fec8` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003fec8` | `0x8003ff40` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ff40` | `0x8003ffb8` | 120 | `h_DUP13` | UNCONVERTED |
| `0x8003ffb8` | `0x80040030` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040030` | `0x800400a8` | 120 | `h_DUP15` | UNCONVERTED |
| `0x800400a8` | `0x80040120` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040120` | `0x80040190` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x80040190` | `0x80040200` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x80040200` | `0x80040270` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x80040270` | `0x800402e0` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x800402e0` | `0x80040350` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x80040350` | `0x800403c0` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x800403c0` | `0x80040430` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040430` | `0x800404a0` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x800404a0` | `0x80040510` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x80040510` | `0x80040580` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x80040580` | `0x800405f0` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x800405f0` | `0x80040660` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x80040660` | `0x800406d0` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x800406d0` | `0x80040740` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x80040740` | `0x800407b0` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x800407b0` | `0x80040820` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040820` | `0x80040838` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040838` | `0x8004084c` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x8004084c` | `0x800408d8` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x800408d8` | `0x800408f0` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x800408f0` | `0x80040904` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040904` | `0x8004098c` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x8004098c` | `0x800409a4` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x800409a4` | `0x800409b8` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x800409b8` | `0x800409d8` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x800409d8` | `0x800409e0` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x800409e0` | `0x800409ec` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x800409ec` | `0x800409f0` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x800409f0` | `0x80040a74` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040a74` | `0x80040b1c` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b1c` | `0x80040c50` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040c50` | `0x80040cf8` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040cf8` | `0x80040df0` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040df0` | `0x80040e88` | 152 | `h_LT` | UNCONVERTED |
| `0x80040e88` | `0x80040f20` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f20` | `0x80040fb4` | 148 | `h_SLT` | UNCONVERTED |
| `0x80040fb4` | `0x80041048` | 148 | `h_SGT` | UNCONVERTED |
| `0x80041048` | `0x800410cc` | 132 | `h_EQ` | UNCONVERTED |
| `0x800410cc` | `0x8004112c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004112c` | `0x800411a0` | 116 | `h_AND` | UNCONVERTED |
| `0x800411a0` | `0x80041214` | 116 | `h_OR` | UNCONVERTED |
| `0x80041214` | `0x80041288` | 116 | `h_XOR` | UNCONVERTED |
| `0x80041288` | `0x800412e8` | 96 | `h_NOT` | UNCONVERTED |
| `0x800412e8` | `0x800413d4` | 236 | `h_BYTE` | UNCONVERTED |
| `0x800413d4` | `0x80041574` | 416 | `h_SHL` | UNCONVERTED |
| `0x80041574` | `0x80041714` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041714` | `0x800418c8` | 436 | `h_SAR` | UNCONVERTED |
| `0x800418c8` | `0x800419c8` | 256 | `h_CLZ` | UNCONVERTED |
| `0x800419c8` | `0x800419fc` | 52 | `h_POP` | UNCONVERTED |
| `0x800419fc` | `0x80041d48` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041d48` | `0x80042028` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042028` | `0x80042148` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x80042148` | `0x8004218c` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x8004218c` | `0x800421d0` | 68 | `h_GAS` | UNCONVERTED |
| `0x800421d0` | `0x80042220` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042220` | `0x80042270` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x80042270` | `0x800422c0` | 80 | `h_CALLER` | UNCONVERTED |
| `0x800422c0` | `0x80042310` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80042310` | `0x80042360` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x80042360` | `0x800423b0` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x800423b0` | `0x80042400` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80042400` | `0x80042450` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x80042450` | `0x800424a0` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x800424a0` | `0x800424f0` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x800424f0` | `0x80042540` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x80042540` | `0x80042590` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x80042590` | `0x800425e0` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x800425e0` | `0x80042630` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042630` | `0x80042680` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x80042680` | `0x80042718` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042718` | `0x80042804` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042804` | `0x80042848` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x80042848` | `0x80042a64` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042a64` | `0x80042c34` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c34` | `0x80042c78` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042c78` | `0x80042e44` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042e44` | `0x80042e4c` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042e4c` | `0x80042f0c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f0c` | `0x80043000` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80043000` | `0x80043044` | 68 | `h_PC` | UNCONVERTED |
| `0x800432cc` | `0x800435c0` | 756 | `h_LOG0` | UNCONVERTED |
| `0x800435c0` | `0x800438d4` | 788 | `h_LOG1` | UNCONVERTED |
| `0x800438d4` | `0x80043c08` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c08` | `0x80043f5c` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043f5c` | `0x800442d0` | 884 | `h_LOG4` | UNCONVERTED |
| `0x800442d0` | `0x80044578` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x80044578` | `0x80044880` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x80044880` | `0x80044eec` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044eec` | `0x80045494` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x80045494` | `0x80045a14` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a14` | `0x800462a0` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x800462a0` | `0x8004638c` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x8004638c` | `0x8004645c` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x8004645c` | `0x800466dc` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x800466dc` | `0x80047074` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x80047074` | `0x80047658` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x80047658` | `0x80047674` | 28 | `h_INVALID` | UNCONVERTED |
| `0x80047674` | `0x80048b98` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048b98` | `0x80048be4` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048be4` | `0x80048d88` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048d88` | `0x80049b50` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049b50` | `0x8004bdfc` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004bdfc` | `0x8004cf74` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cf74` | `0x8004dbd8` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dbd8` | `0x8004e9e0` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004e9e0` | `0x8004f644` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f644` | `0x8004fefc` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004fefc` | `0x800507f0` | 2292 | `h_DIV` | UNCONVERTED |
| `0x800507f0` | `0x80050d8c` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050d8c` | `0x80051438` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051438` | `0x80051458` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x80051458` | `0x80051b04` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b04` | `0x80051b24` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b24` | `0x80052454` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x80052454` | `0x800527a0` | 844 | `h_EXP` | UNCONVERTED |
| `0x800527a0` | `0x80052910` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052910` | `0x80052914` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052914` | `0x8005299c` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x8005299c` | `0x80052b90` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052b90` | `0x80052bc0` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052bc0` | `0x80052bd4` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052bd4` | `0x80052be4` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052be4` | `0x80052c14` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c14` | `0x80052e08` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e08` | `0x80052e38` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e38` | `0x80052e4c` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052e4c` | `0x80052e5c` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052e5c` | `0x80052e8c` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052e8c` | `0x80052eb0` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052eb0` | `0x80052ee0` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052ee0` | `0x800530d4` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x800530d4` | `0x80053104` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053104` | `0x80053118` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053118` | `0x80053128` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053128` | `0x80053158` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x80053158` | `0x8005334c` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x8005334c` | `0x8005337c` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x8005337c` | `0x80053390` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053390` | `0x800533a0` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x800533a0` | `0x800533d0` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x800533d0` | `0x800535c4` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x800535c4` | `0x800535f4` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x800535f4` | `0x80053608` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053608` | `0x80053618` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053618` | `0x80053648` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053648` | `0x80053648` | 0 | `.exit_label` | UNCONVERTED |
| `0x80053648` | `0x80053664` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053f24` | `0x80054054` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x80054054` | `0x800540b0` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x800540b0` | `0x800540d0` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x800540d0` | `0x8005420c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x800543dc` | `0x800543e8` | 12 | `requests_hash_verify` | TAIL |
