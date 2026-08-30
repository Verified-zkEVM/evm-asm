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
not linked** (88 of 564 today — gas helpers etc.
awaiting wiring); they are excluded from `guestImageEntries` (the image
`CodeReq` must reflect the emitted ELF) and are NOT gaps.

## 1. Summary

`.text` = [0x80000000, 0x80054448), 345160 bytes (`RegionMap.textSizeBytes = 0x54448`)

- symbols in `.text`: 909 (476 converted, 433 unconverted)
- covered by converted `_prog`s: 133280 bytes (38.61%)
- NOT covered: 211880 bytes (61.39%), 434 ranges

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
| `0x8002ab04` | `0x8002ada0` | 668 | `b1_sender_count_table` | UNCONVERTED |
| `0x8002ada0` | `0x8002add8` | 56 | `b1sc_write_entry` | UNCONVERTED |
| `0x8002ca34` | `0x8002cf2c` | 1272 | `stateless_verdict_v2` | UNCONVERTED |
| `0x8002cf2c` | `0x8002db50` | 3108 | `block_verdict_deferred_system_requests` | UNCONVERTED |
| `0x8002db50` | `0x8002e120` | 1488 | `precompile_shared_select_price` | UNCONVERTED |
| `0x8002e120` | `0x8002fae0` | 6592 | `precompile_shared_execute` | UNCONVERTED |
| `0x8002fae0` | `0x8002fb04` | 36 | `runtime_dispatcher_prepare_only` | UNCONVERTED |
| `0x8002fb04` | `0x8002fb20` | 28 | `runtime_dispatcher_prepare_only_return` | UNCONVERTED |
| `0x8002fb20` | `0x8002fde4` | 708 | `runtime_dispatcher_call` | UNCONVERTED |
| `0x8002fde4` | `0x8002fdf4` | 16 | `.blob_hash_count_ok` | UNCONVERTED |
| `0x8002fdf4` | `0x8002fe28` | 52 | `.blob_hash_copy_loop` | UNCONVERTED |
| `0x8002fe28` | `0x8002fe40` | 24 | `.blob_hash_copy_done` | UNCONVERTED |
| `0x8002fe40` | `0x8002fe50` | 16 | `.blockhash_count_ok` | UNCONVERTED |
| `0x8002fe50` | `0x8002fe84` | 52 | `.blockhash_copy_loop` | UNCONVERTED |
| `0x8002fe84` | `0x8002fe8c` | 8 | `.blockhash_copy_done` | UNCONVERTED |
| `0x8002fe8c` | `0x8002ff38` | 172 | `.env_trailer_copy_loop` | UNCONVERTED |
| `0x8002ff38` | `0x8002ff44` | 12 | `.runtime_tx_gas_no_create` | UNCONVERTED |
| `0x8002ff44` | `0x8002ff6c` | 40 | `.runtime_tx_gas_self_cmp` | UNCONVERTED |
| `0x8002ff6c` | `0x8002ffac` | 64 | `.runtime_tx_gas_not_self` | UNCONVERTED |
| `0x8002ffac` | `0x8002ffdc` | 48 | `.runtime_tx_gas_recipient_done` | UNCONVERTED |
| `0x8002ffdc` | `0x8002ffdc` | 0 | `.runtime_tx_gas_data_loop` | UNCONVERTED |
| `0x8002ffdc` | `0x8002fff4` | 24 | `.runtime_tx_gas_data_span_ready` | UNCONVERTED |
| `0x8002fff4` | `0x8002fffc` | 8 | `.runtime_tx_gas_zero_byte` | UNCONVERTED |
| `0x8002fffc` | `0x80030008` | 12 | `.runtime_tx_gas_data_step` | UNCONVERTED |
| `0x80030008` | `0x80030020` | 24 | `.runtime_tx_gas_create_words` | UNCONVERTED |
| `0x80030020` | `0x80030038` | 24 | `.runtime_tx_gas_access_list` | UNCONVERTED |
| `0x80030038` | `0x8003004c` | 20 | `.runtime_tx_gas_addr_loop` | UNCONVERTED |
| `0x8003004c` | `0x8003006c` | 32 | `.runtime_tx_gas_access_slots` | UNCONVERTED |
| `0x8003006c` | `0x80030080` | 20 | `.runtime_tx_gas_slot_loop` | UNCONVERTED |
| `0x80030080` | `0x800300ac` | 44 | `.runtime_tx_gas_check` | UNCONVERTED |
| `0x800300ac` | `0x800300f4` | 72 | `.runtime_tx_auth_regular_charge_done` | UNCONVERTED |
| `0x800300f4` | `0x800301d4` | 224 | `.runtime_tx_gas_no_reservoir` | UNCONVERTED |
| `0x800301d4` | `0x80030284` | 176 | `.runtime_tx_auth_checkpoint_done` | UNCONVERTED |
| `0x80030284` | `0x800302a4` | 32 | `.runtime_tx_auth_phase_oog` | UNCONVERTED |
| `0x800302a4` | `0x80030318` | 116 | `.runtime_tx_auth_exec_done` | UNCONVERTED |
| `0x80030318` | `0x80030328` | 16 | `.runtime_tx_auth_state_spill` | UNCONVERTED |
| `0x80030328` | `0x80030334` | 12 | `.runtime_tx_auth_state_refund_done` | UNCONVERTED |
| `0x80030334` | `0x80030418` | 228 | `.runtime_tx_auth_state_used_done` | UNCONVERTED |
| `0x80030418` | `0x80030440` | 40 | `.runtime_tx_create_state_spill` | UNCONVERTED |
| `0x80030440` | `0x80030454` | 20 | `.runtime_tx_create_state_used` | UNCONVERTED |
| `0x80030454` | `0x80030454` | 0 | `.runtime_tx_create_state_done` | UNCONVERTED |
| `0x80030454` | `0x80030454` | 0 | `.runtime_tx_gas_done` | UNCONVERTED |
| `0x80030454` | `0x80030474` | 32 | `.runtime_tx_prepare_prefix_continue` | UNCONVERTED |
| `0x80030474` | `0x800304a4` | 48 | `.runtime_tx_top_frame_regular_done` | UNCONVERTED |
| `0x800304a4` | `0x800304c8` | 36 | `.runtime_tx_prepare_prefix_oog` | UNCONVERTED |
| `0x800304c8` | `0x800304e8` | 32 | `.runtime_tx_prepare_normal_oog` | UNCONVERTED |
| `0x800304e8` | `0x800304ec` | 4 | `.runtime_tx_prepare_normal_oog_exit` | UNCONVERTED |
| `0x800304ec` | `0x8003058c` | 160 | `.runtime_tx_prepare_body_continue` | UNCONVERTED |
| `0x8003058c` | `0x8003059c` | 16 | `.runtime_tx_post_top_frame_done` | UNCONVERTED |
| `0x8003059c` | `0x800305ac` | 16 | `.runtime_tx_top_level_message_d0_done` | UNCONVERTED |
| `0x800305ac` | `0x800306dc` | 304 | `.runtime_tx_shared_message_body` | UNCONVERTED |
| `0x800306dc` | `0x800306dc` | 0 | `.dispatch_loop` | UNCONVERTED |
| `0x800306dc` | `0x80030878` | 412 | `.runtime_tx_message_entry` | UNCONVERTED |
| `0x80030878` | `0x80030878` | 0 | `.dispatch_resume` | UNCONVERTED |
| `0x80030878` | `0x800308d8` | 96 | `.runtime_tx_child_message_entry` | UNCONVERTED |
| `0x80031690` | `0x800316b8` | 40 | `create_deployed_code_valid` | UNCONVERTED |
| `0x800316b8` | `0x800318c8` | 528 | `create_record_code_effect` | UNCONVERTED |
| `0x800319c8` | `0x80031a74` | 172 | `account_state_promote_delete_reads` | UNCONVERTED |
| `0x80031a74` | `0x80031af8` | 132 | `account_write_touch_current` | UNCONVERTED |
| `0x80031b78` | `0x80031c30` | 184 | `code_state_address_set_insert` | UNCONVERTED |
| `0x80031c30` | `0x80031ca4` | 116 | `code_state_address_set_flag` | UNCONVERTED |
| `0x80031ca4` | `0x80031e68` | 452 | `create_creator_nonce_use` | UNCONVERTED |
| `0x80031e68` | `0x80031ed8` | 112 | `create_creator_nonce_undo_to` | UNCONVERTED |
| `0x80031ed8` | `0x80031f50` | 120 | `create_creator_nonce_current` | UNCONVERTED |
| `0x80031f50` | `0x80032100` | 432 | `create_creator_nonce_seed_one` | UNCONVERTED |
| `0x80032100` | `0x8003217c` | 124 | `create_creator_nonce_contains` | UNCONVERTED |
| `0x8003217c` | `0x800321cc` | 80 | `modexp_be_to_le` | UNCONVERTED |
| `0x800321cc` | `0x8003221c` | 80 | `modexp_le_to_be` | UNCONVERTED |
| `0x8003221c` | `0x8003224c` | 48 | `modexp_iszero` | UNCONVERTED |
| `0x8003224c` | `0x80032290` | 68 | `modexp_cmpge` | UNCONVERTED |
| `0x80032290` | `0x800322d4` | 68 | `modexp_sub` | UNCONVERTED |
| `0x800322d4` | `0x80032384` | 176 | `modexp_mul` | UNCONVERTED |
| `0x80032384` | `0x800324e0` | 348 | `modexp_binmod` | UNCONVERTED |
| `0x800324e0` | `0x800327dc` | 764 | `zkvm_modexp` | UNCONVERTED |
| `0x800327dc` | `0x800329b8` | 476 | `zkvm_ripemd160` | UNCONVERTED |
| `0x800329b8` | `0x80032a64` | 172 | `ripemd_compress` | UNCONVERTED |
| `0x80032a64` | `0x80032bdc` | 376 | `ripemd_line160` | UNCONVERTED |
| `0x80032bdc` | `0x80032da8` | 460 | `evm_storage_access_charge_key` | UNCONVERTED |
| `0x80032da8` | `0x80032edc` | 308 | `sstore_gas_refund_outcome` | UNCONVERTED |
| `0x80032fcc` | `0x800330a8` | 220 | `runtime_access_account_seed` | UNCONVERTED |
| `0x800330a8` | `0x800331f8` | 336 | `runtime_access_seed_initial_accounts` | UNCONVERTED |
| `0x800331f8` | `0x800333d4` | 476 | `runtime_access_account_charge` | UNCONVERTED |
| `0x80033584` | `0x80033770` | 492 | `eip7708_append_synthetic_log` | UNCONVERTED |
| `0x80033770` | `0x800337c4` | 84 | `eip7708_append_transfer_log` | UNCONVERTED |
| `0x800337c4` | `0x8003380c` | 72 | `eip7708_append_burn_log` | UNCONVERTED |
| `0x8003380c` | `0x800338e0` | 212 | `dispatcher_reemit_pending_tl` | UNCONVERTED |
| `0x800338e0` | `0x800339c0` | 224 | `dispatcher_seed_pending_upfront_sender_balance` | UNCONVERTED |
| `0x800339c0` | `0x80033b78` | 440 | `dispatcher_seed_pending_value_transfer` | UNCONVERTED |
| `0x80034590` | `0x8003460c` | 124 | `zkvm_bls12_g1_add` | UNCONVERTED |
| `0x8003460c` | `0x800346f8` | 236 | `zkvm_bls12_g1_msm` | UNCONVERTED |
| `0x80034d5c` | `0x80034dcc` | 112 | `zkvm_bn254_g1_add` | UNCONVERTED |
| `0x80034dcc` | `0x80034e2c` | 96 | `zkvm_bn254_g1_mul` | UNCONVERTED |
| `0x80035208` | `0x8003525c` | 84 | `bnq_sub` | UNCONVERTED |
| `0x80035424` | `0x80035690` | 620 | `bnq_pt_double` | UNCONVERTED |
| `0x80035690` | `0x800359d0` | 832 | `bnq_pt_add` | UNCONVERTED |
| `0x800359d0` | `0x80035c80` | 688 | `bnq_linefunc` | UNCONVERTED |
| `0x80035c80` | `0x80035fb4` | 820 | `bng2_double` | UNCONVERTED |
| `0x80035fb4` | `0x8003633c` | 904 | `bng2_add` | UNCONVERTED |
| `0x8003633c` | `0x8003645c` | 288 | `bng2_subgroup_ok` | UNCONVERTED |
| `0x8003647c` | `0x800368ac` | 1072 | `bnq_miller_accumulate` | UNCONVERTED |
| `0x800368ac` | `0x80036cf0` | 1092 | `zkvm_bn254_pairing` | UNCONVERTED |
| `0x80036d44` | `0x80036ef0` | 428 | `zkvm_blake2f` | UNCONVERTED |
| `0x80037364` | `0x80037528` | 452 | `zkvm_kzg_point_eval` | UNCONVERTED |
| `0x80037cb8` | `0x80037f90` | 728 | `zkvm_secp256r1_verify` | UNCONVERTED |
| `0x8003887c` | `0x8003890c` | 144 | `zkvm_bls12_g2_add` | UNCONVERTED |
| `0x8003890c` | `0x800389dc` | 208 | `zkvm_bls12_g2_msm` | UNCONVERTED |
| `0x80038bb4` | `0x80038c10` | 92 | `blq_sub` | UNCONVERTED |
| `0x80038e00` | `0x8003906c` | 620 | `blq_pt_double` | UNCONVERTED |
| `0x8003906c` | `0x8003938c` | 800 | `blq_pt_add` | UNCONVERTED |
| `0x8003938c` | `0x8003963c` | 688 | `blq_linefunc` | UNCONVERTED |
| `0x8003963c` | `0x80039818` | 476 | `blq_miller_accumulate` | UNCONVERTED |
| `0x80039818` | `0x80039b60` | 840 | `zkvm_bls12_pairing` | UNCONVERTED |
| `0x80039cac` | `0x8003b510` | 6244 | `zkvm_bls12_map_fp_to_g1` | UNCONVERTED |
| `0x8003b510` | `0x8003c74c` | 4668 | `zkvm_bls12_map_fp2_to_g2` | UNCONVERTED |
| `0x8003c870` | `0x8003c98c` | 284 | `call_frame_set_call_env` | UNCONVERTED |
| `0x8003c9cc` | `0x8003cf68` | 1436 | `call_frame_descend` | UNCONVERTED |
| `0x8003cf68` | `0x8003d278` | 784 | `create_frame_descend` | UNCONVERTED |
| `0x8003d278` | `0x8003d280` | 8 | `record_nonstorage_effect` | UNCONVERTED |
| `0x8003d280` | `0x8003d284` | 4 | `record_nonstorage_effect_after_account_state` | UNCONVERTED |
| `0x8003d284` | `0x8003d468` | 484 | `record_nonstorage_effect_nonce_only_after_account_state` | UNCONVERTED |
| `0x8003d560` | `0x8003d7a8` | 584 | `nonstorage_apply_destroyed_norm` | UNCONVERTED |
| `0x8003d7a8` | `0x8003de0c` | 1636 | `frame_return` | UNCONVERTED |
| `0x8003de0c` | `0x8003df28` | 284 | `sparse_window_read` | UNCONVERTED |
| `0x8003df28` | `0x8003e140` | 536 | `sparse_window_write` | UNCONVERTED |
| `0x8003e140` | `0x8003e180` | 64 | `h_PUSH0` | UNCONVERTED |
| `0x8003e180` | `0x8003e1c8` | 72 | `h_PUSH1` | UNCONVERTED |
| `0x8003e1c8` | `0x8003e218` | 80 | `h_PUSH2` | UNCONVERTED |
| `0x8003e218` | `0x8003e270` | 88 | `h_PUSH3` | UNCONVERTED |
| `0x8003e270` | `0x8003e2d0` | 96 | `h_PUSH4` | UNCONVERTED |
| `0x8003e2d0` | `0x8003e338` | 104 | `h_PUSH5` | UNCONVERTED |
| `0x8003e338` | `0x8003e3a8` | 112 | `h_PUSH6` | UNCONVERTED |
| `0x8003e3a8` | `0x8003e420` | 120 | `h_PUSH7` | UNCONVERTED |
| `0x8003e420` | `0x8003e4a0` | 128 | `h_PUSH8` | UNCONVERTED |
| `0x8003e4a0` | `0x8003e528` | 136 | `h_PUSH9` | UNCONVERTED |
| `0x8003e528` | `0x8003e5b8` | 144 | `h_PUSH10` | UNCONVERTED |
| `0x8003e5b8` | `0x8003e650` | 152 | `h_PUSH11` | UNCONVERTED |
| `0x8003e650` | `0x8003e6f0` | 160 | `h_PUSH12` | UNCONVERTED |
| `0x8003e6f0` | `0x8003e798` | 168 | `h_PUSH13` | UNCONVERTED |
| `0x8003e798` | `0x8003e848` | 176 | `h_PUSH14` | UNCONVERTED |
| `0x8003e848` | `0x8003e900` | 184 | `h_PUSH15` | UNCONVERTED |
| `0x8003e900` | `0x8003e9c0` | 192 | `h_PUSH16` | UNCONVERTED |
| `0x8003e9c0` | `0x8003ea88` | 200 | `h_PUSH17` | UNCONVERTED |
| `0x8003ea88` | `0x8003eb58` | 208 | `h_PUSH18` | UNCONVERTED |
| `0x8003eb58` | `0x8003ec30` | 216 | `h_PUSH19` | UNCONVERTED |
| `0x8003ec30` | `0x8003ed10` | 224 | `h_PUSH20` | UNCONVERTED |
| `0x8003ed10` | `0x8003edf8` | 232 | `h_PUSH21` | UNCONVERTED |
| `0x8003edf8` | `0x8003eee8` | 240 | `h_PUSH22` | UNCONVERTED |
| `0x8003eee8` | `0x8003efe0` | 248 | `h_PUSH23` | UNCONVERTED |
| `0x8003efe0` | `0x8003f0e0` | 256 | `h_PUSH24` | UNCONVERTED |
| `0x8003f0e0` | `0x8003f1e8` | 264 | `h_PUSH25` | UNCONVERTED |
| `0x8003f1e8` | `0x8003f2f8` | 272 | `h_PUSH26` | UNCONVERTED |
| `0x8003f2f8` | `0x8003f410` | 280 | `h_PUSH27` | UNCONVERTED |
| `0x8003f410` | `0x8003f530` | 288 | `h_PUSH28` | UNCONVERTED |
| `0x8003f530` | `0x8003f658` | 296 | `h_PUSH29` | UNCONVERTED |
| `0x8003f658` | `0x8003f788` | 304 | `h_PUSH30` | UNCONVERTED |
| `0x8003f788` | `0x8003f8c0` | 312 | `h_PUSH31` | UNCONVERTED |
| `0x8003f8c0` | `0x8003fa00` | 320 | `h_PUSH32` | UNCONVERTED |
| `0x8003fa00` | `0x8003fa78` | 120 | `h_DUP1` | UNCONVERTED |
| `0x8003fa78` | `0x8003faf0` | 120 | `h_DUP2` | UNCONVERTED |
| `0x8003faf0` | `0x8003fb68` | 120 | `h_DUP3` | UNCONVERTED |
| `0x8003fb68` | `0x8003fbe0` | 120 | `h_DUP4` | UNCONVERTED |
| `0x8003fbe0` | `0x8003fc58` | 120 | `h_DUP5` | UNCONVERTED |
| `0x8003fc58` | `0x8003fcd0` | 120 | `h_DUP6` | UNCONVERTED |
| `0x8003fcd0` | `0x8003fd48` | 120 | `h_DUP7` | UNCONVERTED |
| `0x8003fd48` | `0x8003fdc0` | 120 | `h_DUP8` | UNCONVERTED |
| `0x8003fdc0` | `0x8003fe38` | 120 | `h_DUP9` | UNCONVERTED |
| `0x8003fe38` | `0x8003feb0` | 120 | `h_DUP10` | UNCONVERTED |
| `0x8003feb0` | `0x8003ff28` | 120 | `h_DUP11` | UNCONVERTED |
| `0x8003ff28` | `0x8003ffa0` | 120 | `h_DUP12` | UNCONVERTED |
| `0x8003ffa0` | `0x80040018` | 120 | `h_DUP13` | UNCONVERTED |
| `0x80040018` | `0x80040090` | 120 | `h_DUP14` | UNCONVERTED |
| `0x80040090` | `0x80040108` | 120 | `h_DUP15` | UNCONVERTED |
| `0x80040108` | `0x80040180` | 120 | `h_DUP16` | UNCONVERTED |
| `0x80040180` | `0x800401f0` | 112 | `h_SWAP1` | UNCONVERTED |
| `0x800401f0` | `0x80040260` | 112 | `h_SWAP2` | UNCONVERTED |
| `0x80040260` | `0x800402d0` | 112 | `h_SWAP3` | UNCONVERTED |
| `0x800402d0` | `0x80040340` | 112 | `h_SWAP4` | UNCONVERTED |
| `0x80040340` | `0x800403b0` | 112 | `h_SWAP5` | UNCONVERTED |
| `0x800403b0` | `0x80040420` | 112 | `h_SWAP6` | UNCONVERTED |
| `0x80040420` | `0x80040490` | 112 | `h_SWAP7` | UNCONVERTED |
| `0x80040490` | `0x80040500` | 112 | `h_SWAP8` | UNCONVERTED |
| `0x80040500` | `0x80040570` | 112 | `h_SWAP9` | UNCONVERTED |
| `0x80040570` | `0x800405e0` | 112 | `h_SWAP10` | UNCONVERTED |
| `0x800405e0` | `0x80040650` | 112 | `h_SWAP11` | UNCONVERTED |
| `0x80040650` | `0x800406c0` | 112 | `h_SWAP12` | UNCONVERTED |
| `0x800406c0` | `0x80040730` | 112 | `h_SWAP13` | UNCONVERTED |
| `0x80040730` | `0x800407a0` | 112 | `h_SWAP14` | UNCONVERTED |
| `0x800407a0` | `0x80040810` | 112 | `h_SWAP15` | UNCONVERTED |
| `0x80040810` | `0x80040880` | 112 | `h_SWAP16` | UNCONVERTED |
| `0x80040880` | `0x80040898` | 24 | `h_DUPN` | UNCONVERTED |
| `0x80040898` | `0x800408ac` | 20 | `.dupn_imm_loaded` | UNCONVERTED |
| `0x800408ac` | `0x80040938` | 140 | `.dupn_imm_valid` | UNCONVERTED |
| `0x80040938` | `0x80040950` | 24 | `h_SWAPN` | UNCONVERTED |
| `0x80040950` | `0x80040964` | 20 | `.swapn_imm_loaded` | UNCONVERTED |
| `0x80040964` | `0x800409ec` | 136 | `.swapn_imm_valid` | UNCONVERTED |
| `0x800409ec` | `0x80040a04` | 24 | `h_EXCHANGE` | UNCONVERTED |
| `0x80040a04` | `0x80040a18` | 20 | `.exchange_imm_loaded` | UNCONVERTED |
| `0x80040a18` | `0x80040a38` | 32 | `.exchange_imm_valid` | UNCONVERTED |
| `0x80040a38` | `0x80040a40` | 8 | `.exchange_q_lt_r` | UNCONVERTED |
| `0x80040a40` | `0x80040a4c` | 12 | `.exchange_decoded` | UNCONVERTED |
| `0x80040a4c` | `0x80040a50` | 4 | `.exchange_depth_m` | UNCONVERTED |
| `0x80040a50` | `0x80040ad4` | 132 | `.exchange_depth_ready` | UNCONVERTED |
| `0x80040ad4` | `0x80040b7c` | 168 | `h_ADD` | UNCONVERTED |
| `0x80040b7c` | `0x80040cb0` | 308 | `h_MUL` | UNCONVERTED |
| `0x80040cb0` | `0x80040d58` | 168 | `h_SUB` | UNCONVERTED |
| `0x80040d58` | `0x80040e50` | 248 | `h_SIGNEXTEND` | UNCONVERTED |
| `0x80040e50` | `0x80040ee8` | 152 | `h_LT` | UNCONVERTED |
| `0x80040ee8` | `0x80040f80` | 152 | `h_GT` | UNCONVERTED |
| `0x80040f80` | `0x80041014` | 148 | `h_SLT` | UNCONVERTED |
| `0x80041014` | `0x800410a8` | 148 | `h_SGT` | UNCONVERTED |
| `0x800410a8` | `0x8004112c` | 132 | `h_EQ` | UNCONVERTED |
| `0x8004112c` | `0x8004118c` | 96 | `h_ISZERO` | UNCONVERTED |
| `0x8004118c` | `0x80041200` | 116 | `h_AND` | UNCONVERTED |
| `0x80041200` | `0x80041274` | 116 | `h_OR` | UNCONVERTED |
| `0x80041274` | `0x800412e8` | 116 | `h_XOR` | UNCONVERTED |
| `0x800412e8` | `0x80041348` | 96 | `h_NOT` | UNCONVERTED |
| `0x80041348` | `0x80041434` | 236 | `h_BYTE` | UNCONVERTED |
| `0x80041434` | `0x800415d4` | 416 | `h_SHL` | UNCONVERTED |
| `0x800415d4` | `0x80041774` | 416 | `h_SHR` | UNCONVERTED |
| `0x80041774` | `0x80041928` | 436 | `h_SAR` | UNCONVERTED |
| `0x80041928` | `0x80041a28` | 256 | `h_CLZ` | UNCONVERTED |
| `0x80041a28` | `0x80041a5c` | 52 | `h_POP` | UNCONVERTED |
| `0x80041a5c` | `0x80041da8` | 844 | `h_MLOAD` | UNCONVERTED |
| `0x80041da8` | `0x80042088` | 736 | `h_MSTORE` | UNCONVERTED |
| `0x80042088` | `0x800421a8` | 288 | `h_MSTORE8` | UNCONVERTED |
| `0x800421a8` | `0x800421ec` | 68 | `h_MSIZE` | UNCONVERTED |
| `0x800421ec` | `0x80042230` | 68 | `h_GAS` | UNCONVERTED |
| `0x80042230` | `0x80042280` | 80 | `h_ADDRESS` | UNCONVERTED |
| `0x80042280` | `0x800422d0` | 80 | `h_ORIGIN` | UNCONVERTED |
| `0x800422d0` | `0x80042320` | 80 | `h_CALLER` | UNCONVERTED |
| `0x80042320` | `0x80042370` | 80 | `h_CALLVALUE` | UNCONVERTED |
| `0x80042370` | `0x800423c0` | 80 | `h_GASPRICE` | UNCONVERTED |
| `0x800423c0` | `0x80042410` | 80 | `h_COINBASE` | UNCONVERTED |
| `0x80042410` | `0x80042460` | 80 | `h_TIMESTAMP` | UNCONVERTED |
| `0x80042460` | `0x800424b0` | 80 | `h_NUMBER` | UNCONVERTED |
| `0x800424b0` | `0x80042500` | 80 | `h_PREVRANDAO` | UNCONVERTED |
| `0x80042500` | `0x80042550` | 80 | `h_GASLIMIT` | UNCONVERTED |
| `0x80042550` | `0x800425a0` | 80 | `h_CHAINID` | UNCONVERTED |
| `0x800425a0` | `0x800425f0` | 80 | `h_SELFBALANCE` | UNCONVERTED |
| `0x800425f0` | `0x80042640` | 80 | `h_BASEFEE` | UNCONVERTED |
| `0x80042640` | `0x80042690` | 80 | `h_SLOTNUM` | UNCONVERTED |
| `0x80042690` | `0x800426e0` | 80 | `h_BLOBBASEFEE` | UNCONVERTED |
| `0x800426e0` | `0x80042778` | 152 | `h_BLOBHASH` | UNCONVERTED |
| `0x80042778` | `0x80042864` | 236 | `h_BLOCKHASH` | UNCONVERTED |
| `0x80042864` | `0x800428a8` | 68 | `h_CALLDATASIZE` | UNCONVERTED |
| `0x800428a8` | `0x80042ac4` | 540 | `h_CALLDATALOAD` | UNCONVERTED |
| `0x80042ac4` | `0x80042c94` | 464 | `h_CALLDATACOPY` | UNCONVERTED |
| `0x80042c94` | `0x80042cd8` | 68 | `h_CODESIZE` | UNCONVERTED |
| `0x80042cd8` | `0x80042ea4` | 460 | `h_CODECOPY` | UNCONVERTED |
| `0x80042ea4` | `0x80042eac` | 8 | `h_JUMPDEST` | UNCONVERTED |
| `0x80042eac` | `0x80042f6c` | 192 | `h_JUMP` | UNCONVERTED |
| `0x80042f6c` | `0x80043060` | 244 | `h_JUMPI` | UNCONVERTED |
| `0x80043060` | `0x800430a4` | 68 | `h_PC` | UNCONVERTED |
| `0x8004332c` | `0x80043620` | 756 | `h_LOG0` | UNCONVERTED |
| `0x80043620` | `0x80043934` | 788 | `h_LOG1` | UNCONVERTED |
| `0x80043934` | `0x80043c68` | 820 | `h_LOG2` | UNCONVERTED |
| `0x80043c68` | `0x80043fbc` | 852 | `h_LOG3` | UNCONVERTED |
| `0x80043fbc` | `0x80044330` | 884 | `h_LOG4` | UNCONVERTED |
| `0x80044330` | `0x800445d8` | 680 | `h_BALANCE` | UNCONVERTED |
| `0x800445d8` | `0x800448e0` | 776 | `h_EXTCODESIZE` | UNCONVERTED |
| `0x800448e0` | `0x80044f4c` | 1644 | `h_EXTCODEHASH` | UNCONVERTED |
| `0x80044f4c` | `0x800454f4` | 1448 | `h_EXTCODECOPY` | UNCONVERTED |
| `0x800454f4` | `0x80045a74` | 1408 | `h_SLOAD` | UNCONVERTED |
| `0x80045a74` | `0x80046300` | 2188 | `h_SSTORE` | UNCONVERTED |
| `0x80046300` | `0x800463ec` | 236 | `h_TLOAD` | UNCONVERTED |
| `0x800463ec` | `0x800464bc` | 208 | `h_TSTORE` | UNCONVERTED |
| `0x800464bc` | `0x8004673c` | 640 | `h_MCOPY` | UNCONVERTED |
| `0x8004673c` | `0x800470d4` | 2456 | `h_RETURN` | UNCONVERTED |
| `0x800470d4` | `0x800476b8` | 1508 | `h_REVERT` | UNCONVERTED |
| `0x800476b8` | `0x800476d4` | 28 | `h_INVALID` | UNCONVERTED |
| `0x800476d4` | `0x80048bf8` | 5412 | `h_SELFDESTRUCT` | UNCONVERTED |
| `0x80048bf8` | `0x80048c44` | 76 | `h_RETURNDATASIZE` | UNCONVERTED |
| `0x80048c44` | `0x80048de8` | 420 | `h_RETURNDATACOPY` | UNCONVERTED |
| `0x80048de8` | `0x80049bb0` | 3528 | `h_CREATE` | UNCONVERTED |
| `0x80049bb0` | `0x8004be5c` | 8876 | `h_CALL` | UNCONVERTED |
| `0x8004be5c` | `0x8004cfd4` | 4472 | `h_CALLCODE` | UNCONVERTED |
| `0x8004cfd4` | `0x8004dc38` | 3172 | `h_DELEGATECALL` | UNCONVERTED |
| `0x8004dc38` | `0x8004ea40` | 3592 | `h_CREATE2` | UNCONVERTED |
| `0x8004ea40` | `0x8004f6a4` | 3172 | `h_STATICCALL` | UNCONVERTED |
| `0x8004f6a4` | `0x8004ff5c` | 2232 | `h_MULMOD` | UNCONVERTED |
| `0x8004ff5c` | `0x80050850` | 2292 | `h_DIV` | UNCONVERTED |
| `0x80050850` | `0x80050dec` | 1436 | `h_MOD` | UNCONVERTED |
| `0x80050dec` | `0x80051498` | 1708 | `h_SDIV` | UNCONVERTED |
| `0x80051498` | `0x800514b8` | 32 | `h_SDIV_done` | UNCONVERTED |
| `0x800514b8` | `0x80051b64` | 1708 | `h_SMOD` | UNCONVERTED |
| `0x80051b64` | `0x80051b84` | 32 | `h_SMOD_done` | UNCONVERTED |
| `0x80051b84` | `0x800524b4` | 2352 | `h_ADDMOD` | UNCONVERTED |
| `0x800524b4` | `0x80052800` | 844 | `h_EXP` | UNCONVERTED |
| `0x80052800` | `0x80052970` | 368 | `h_STOP` | UNCONVERTED |
| `0x80052970` | `0x80052974` | 4 | `h_invalid` | UNCONVERTED |
| `0x80052974` | `0x800529fc` | 136 | `.exit_static_violation` | UNCONVERTED |
| `0x800529fc` | `0x80052bf0` | 500 | `.exit_invalid` | UNCONVERTED |
| `0x80052bf0` | `0x80052c20` | 48 | `.exit_invalid_top` | UNCONVERTED |
| `0x80052c20` | `0x80052c34` | 20 | `.exit_invalid_prep_auth_halt_done` | UNCONVERTED |
| `0x80052c34` | `0x80052c44` | 16 | `.exit_invalid_hook_done` | UNCONVERTED |
| `0x80052c44` | `0x80052c74` | 48 | `.exit_invalid_top_no_auth_restore` | UNCONVERTED |
| `0x80052c74` | `0x80052e68` | 500 | `.exit_invalid_op` | UNCONVERTED |
| `0x80052e68` | `0x80052e98` | 48 | `.exit_invalid_op_top` | UNCONVERTED |
| `0x80052e98` | `0x80052eac` | 20 | `.exit_invalid_op_prep_auth_halt_done` | UNCONVERTED |
| `0x80052eac` | `0x80052ebc` | 16 | `.exit_invalid_op_hook_done` | UNCONVERTED |
| `0x80052ebc` | `0x80052eec` | 48 | `.exit_invalid_op_top_no_auth_restore` | UNCONVERTED |
| `0x80052eec` | `0x80052f10` | 36 | `.exit_selfdestruct` | UNCONVERTED |
| `0x80052f10` | `0x80052f40` | 48 | `.exit_selfdestruct_top` | UNCONVERTED |
| `0x80052f40` | `0x80053134` | 500 | `.exit_outofgas` | UNCONVERTED |
| `0x80053134` | `0x80053164` | 48 | `.exit_outofgas_top` | UNCONVERTED |
| `0x80053164` | `0x80053178` | 20 | `.exit_outofgas_prep_auth_halt_done` | UNCONVERTED |
| `0x80053178` | `0x80053188` | 16 | `.exit_outofgas_hook_done` | UNCONVERTED |
| `0x80053188` | `0x800531b8` | 48 | `.exit_outofgas_top_no_auth_restore` | UNCONVERTED |
| `0x800531b8` | `0x800533ac` | 500 | `.exit_stack_underflow` | UNCONVERTED |
| `0x800533ac` | `0x800533dc` | 48 | `.exit_stack_underflow_top` | UNCONVERTED |
| `0x800533dc` | `0x800533f0` | 20 | `.exit_stack_underflow_prep_auth_halt_done` | UNCONVERTED |
| `0x800533f0` | `0x80053400` | 16 | `.exit_stack_underflow_hook_done` | UNCONVERTED |
| `0x80053400` | `0x80053430` | 48 | `.exit_stack_underflow_top_no_auth_restore` | UNCONVERTED |
| `0x80053430` | `0x80053624` | 500 | `.exit_stack_overflow` | UNCONVERTED |
| `0x80053624` | `0x80053654` | 48 | `.exit_stack_overflow_top` | UNCONVERTED |
| `0x80053654` | `0x80053668` | 20 | `.exit_stack_overflow_prep_auth_halt_done` | UNCONVERTED |
| `0x80053668` | `0x80053678` | 16 | `.exit_stack_overflow_hook_done` | UNCONVERTED |
| `0x80053678` | `0x800536a8` | 48 | `.exit_stack_overflow_top_no_auth_restore` | UNCONVERTED |
| `0x800536a8` | `0x800536a8` | 0 | `.exit_label` | UNCONVERTED |
| `0x800536a8` | `0x800536c4` | 28 | `.exit_no_epilogue` | UNCONVERTED |
| `0x80053f84` | `0x800540b4` | 304 | `extract_deposit_data` | UNCONVERTED |
| `0x800540b4` | `0x80054110` | 92 | `edd_be32_eq` | UNCONVERTED |
| `0x80054110` | `0x80054130` | 32 | `edd_memcpy` | UNCONVERTED |
| `0x80054130` | `0x8005426c` | 316 | `materialize_log_records` | UNCONVERTED |
| `0x8005443c` | `0x80054448` | 12 | `requests_hash_verify` | TAIL |
