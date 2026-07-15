/-
  EvmAsm.Codegen.Programs.BlockVerdictDataSectionTail

  Tail continuation of the stateless verdict v2 data section. Split out of
  BlockVerdictDataSection.lean to stay within the 1500-line file-size cap.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.CallFrameLayout
import EvmAsm.Codegen.Programs.NonstorageEffectLog
import EvmAsm.Codegen.Programs.AccountTupleSequencesConsistent
import EvmAsm.Codegen.Programs.BalSlotTupleSequence
import EvmAsm.Codegen.Programs.ExecLogSlotTuples
import EvmAsm.Codegen.Programs.BlockVerdictSenderCounts

namespace EvmAsm.Codegen

def ziskStatelessVerdictV2DataSectionTail : String :=
  -- a1vvy step 3: baap_storage_desc/paths/values (~18 MiB) are
  -- UNIONED into call_frame_arena (emitted below) to free the last .data headroom
  -- for the vv4hr.3.4.2 full log-arena lift. They are Phase-H-only (referenced only
  -- in BalAccountApplyPostFields / BlockVerdictSysChange / BlockVerdictStateRoot --
  -- BAL post-field apply + system-change application within the state-root
  -- recompute) and dead during Phase-D dispatch when call_frame_arena is live.
  -- A state-node HP path decodes to <= 2047 nibbles; deletion can join two.
  "mdacc_leaf_path:\n  .zero 2048\n" ++
  "mdacc_collapsed_path:\n  .zero 4096\n" ++
  "bacp_off:\n  .zero 8\n" ++
  "bacp_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bacp_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "baacd_value_len:\n  .zero 8\n" ++
  "baacd_is_empty:\n  .zero 8\n" ++
  "baacd_fail_code:\n  .zero 8\n" ++
  "aie_offset:\n  .zero 8\n" ++
  "aie_length:\n  .zero 8\n" ++
  "aie_empty_code_hash:\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  "bacv_fail_code:\n  .zero 8\n" ++
  "baada_item_off:\n  .zero 8\n" ++
  "baada_item_len:\n  .zero 8\n" ++
  "basr_records:\n  .zero " ++ toString (bsrMaxStateChanges * bsrAccountRecordBytes) ++
  "\nbasr_paths:\n  .zero " ++ toString (bsrMaxStateChanges * bsrPathBytes) ++
  -- a1vvy (2026-06-18): REINSTATED #8513 union to reclaim ~49 MiB of .data
  -- headroom for the 200M log/receipt capacity lifts (vv4hr.3.4.*). basr_values +
  -- basr_accounts are block_state_root replay scratch, referenced ONLY in
  -- BalAccountStateRoot/BlockVerdictStateRoot (Phase H: pre-dispatch state-root
  -- recompute) and dead from the first tx dispatch onward (#8513 gate-verified:
  -- no post-replay reader; re-confirmed 2026-06-18 — no Phase D/T reference).
  -- call_frame_arena is referenced ONLY by CallFrameBase/Descend/Return (Phase D
  -- dispatch). The phases are sequential with disjoint live windows, so the frame
  -- array reuses the basr pair's space as a union. The size relation FLIPPED vs
  -- #8513 (frame ~165 MiB > basr pair ~49 MiB at the 200M capacity), so instead of
  -- the arena aliasing INTO the pair, the pair is coalesced into the FRONT of
  -- call_frame_arena (both labels point inside the arena; the trailing .zero pads
  -- to the full frameArrayBytes). basr_values/basr_accounts are reached via
  -- independent `la`, so relocation is transparent; they stay 32-aligned and keep
  -- their original contiguous delta. Fit + non-overlap pinned by
  -- `frameArray_unions_basr_pair` (CallFrameLayout.lean); ELF ground truth =
  -- readelf -lW top RW LOAD < 0xc0000000.
  "\n.balign 32\n" ++
  "call_frame_arena:\n" ++
  "basr_values:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  "\nbasr_accounts:\n  .zero " ++ toString (bsrMaxStateChanges * bsrEncodedAccountBytes) ++
  -- 4ch8f.73: bv_system_storage_log is NO LONGER unioned here (it is read
  -- post-dispatch, so a frame slot would clobber it). The three baap_storage_*
  -- arenas remain unioned (Phase-H, block_state_root-only, 32-aligned).
  "\nbaap_storage_desc:\n  .zero " ++ toString (bsrMaxBalItems * baapStorageDescBytes) ++
  "\nbaap_storage_paths:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++
  "\nbaap_storage_values:\n  .zero " ++ toString (bsrMaxBalItems * bsrPathBytes) ++
  "\n  .zero " ++ toString (frameArrayBytes - 2 * (bsrMaxStateChanges * bsrEncodedAccountBytes) - (bsrMaxBalItems * baapStorageDescBytes) - 2 * (bsrMaxBalItems * bsrPathBytes)) ++
  "\ncall_frame_arena_end:\n" ++ "\n" ++
  ".balign 8\n" ++
  "evm_memory_pool:\n  .zero " ++ toString evmMemoryPoolBytes ++ "\n" ++
  "evm_memory_pool_end:\n" ++
  ".balign 8\n" ++
  "rb_running_block_bloom:\n  .zero 256\n" ++
  "rb_running_receipt_bloom:\n  .zero 256\n" ++
  "rb_bloom_checkpoints:\n  .zero 262144\n" ++
  "bara_item_off:\n  .zero 8\n" ++
  "bara_item_len:\n  .zero 8\n" ++
  "bara_acct_len:\n  .zero 8\n" ++
  "bara_bal_end:\n  .zero 8\n" ++
  "bara_next_item:\n  .zero 8\n" ++
  "bara_skip_modeled_system:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "bara_path:\n  .zero 64\n" ++
  "bara_acct:\n  .zero 256\n" ++
  ".balign 8\n" ++
  "bara_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  ".balign 8\n" ++
  "bsr_empty_account:\n" ++
  "  .byte 0xf8,0x44,0x80,0x80,0xa0\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  "  .byte 0xa0\n" ++
  "  .byte 0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c\n" ++
  "  .byte 0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0\n" ++
  "  .byte 0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b\n" ++
  "  .byte 0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70\n" ++
  ".balign 8\n" ++
  "iw_empty_trie_root:\n" ++
  "  .byte 0x56,0xe8,0x1f,0x17,0x1b,0xcc,0x55,0xa6\n" ++
  "  .byte 0xff,0x83,0x45,0xe6,0x92,0xc0,0xf8,0x6e\n" ++
  "  .byte 0x5b,0x48,0xe0,0x1b,0x99,0x6c,0xad,0xc0\n" ++
  "  .byte 0x01,0x62,0x2f,0xb5,0xe3,0x63,0xb4,0x21\n" ++
  ".balign 8\n" ++
  "iwd_ptr:\n  .zero 8\n" ++
  "iwd_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "iwd_hash:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "ins_wl:\n  .zero 8\n" ++
  "ins_node_len:\n  .zero 8\n" ++
  "ins_ref_len:\n  .zero 8\n" ++
  "mle_path_off:\n  .zero 8\n" ++
  "mle_path_len:\n  .zero 8\n" ++
  "ins_kcount:\n  .zero 8\n" ++
  "ins_lv_ptr:\n  .zero 8\n" ++
  "ins_lv_len:\n  .zero 8\n" ++
  "ins_m:\n  .zero 8\n" ++
  "ins_niba:\n  .zero 8\n" ++
  "ins_nibb:\n  .zero 8\n" ++
  "ins_node2_len:\n  .zero 8\n" ++
  "ins_ref2_len:\n  .zero 8\n" ++
  ".balign 8\n" ++
  "ins_meta:\n  .zero 48\n" ++
  ".balign 8\n" ++
  "ins_stack:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_k:\n  .zero 2048\n" ++
  ".balign 8\n" ++
  "ins_ref:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_ref2:\n  .zero 64\n" ++
  ".balign 8\n" ++
  "ins_node:\n  .zero 1048576\n" ++
  ".balign 8\n" ++
  "ins_node2:\n  .zero 1048576\n" ++
  ".balign 8\n" ++
  "ins_empty_branch:\n" ++
  "  .byte 0xd1,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80,0x80,0x80,0x80,0x80,0x80,0x80\n" ++
  "  .byte 0x80,0x80\n" ++
  ".balign 8\n" ++
  "mxne_field_len:\n  .zero 8\n" ++
  "mxne_hp_len:\n  .zero 8\n" ++
  "mxne_cursor:\n  .zero 8\n" ++
  "mxne_total_payload:\n  .zero 8\n" ++
  "mxne_hp_buf:\n  .zero 1024\n" ++
  "mxne_payload_buf:\n  .zero 16384\n" ++
  -- .6.4.3.2 contract-dispatch leaf-helper scratch. Shared scratch (zk3_state,
  -- wlh_*, mnk_*, mbc_*, mw_*, mlk_*, ad_*, aa_*, hesr_*) is already provided by
  -- this guest data section, so only the slot/code-side private labels are added
  -- here (deduped against the guest object via nm). The contract-stage/self-
  -- contained/bal-find/bal-storage probe scratch uses unique prefixes (srpc_,
  -- bsc_, bfa_, brsk_) so it cannot collide.
  -- slot_at_index leaf scratch:
  ".balign 8\n" ++
  "si_value_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "si_value_scratch:\n  .zero 256\n" ++
  -- slot_at_header_state_root scratch:
  ".balign 32\n" ++
  "sahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "sahsr_acct_struct:\n  .zero 104\n" ++
  ".balign 32\n" ++
  "sahsr_u256:\n  .zero 32\n" ++
  -- code_at_header_state_root scratch:
  ".balign 32\n" ++
  "cahsr_state_root:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "cahsr_acct_struct:\n  .zero 104\n" ++
  "cahsr_code_offset:\n  .zero 8\n" ++
  "cahsr_code_length:\n  .zero 8\n" ++
  -- stage_runtime_payload_code private scratch:
  ".balign 8\n" ++
  "srpc_ctx:\n  .zero 192\n" ++
  "srpc_exec:\n  .zero 512\n" ++
  "srpc_code:\n  .zero 64\n" ++
  "srpc_env_base:\n  .zero 8\n" ++
  "m29_stage_cur:\n  .zero 8\n" ++
  "m29_stage_count:\n  .zero 8\n" ++
  "m29_stage_table:\n  .zero 8192\n" ++   -- 3vc2p.3b: M29 recent-blockhash table (256x32; default 0 -> inert)
  -- BLOBHASH staging: blob versioned hashes extracted from type-3 txs, written
  -- into the M28 block's blob_hash_count + blob_hashes fields by stage_runtime_payload_code.
  ".balign 8\n" ++
  "m28_blob_stage_count:\n  .zero 8\n" ++
  "m28_blob_stage_table:\n  .zero 512\n" ++  -- 16x32-byte blob hashes (runtime cap in Dispatch.lean)
  -- 3vc2p.3b sub-step B: stage_blockhash_m29 scratch (the ignored offset/length outs + the
  -- pass-1 hash sink) + blockhash_from_witness_headers' number buffer.
  ".balign 32\n" ++
  "m29_hash_tmp:\n  .zero 32\n" ++
  "m29_off_tmp:\n  .zero 8\n" ++
  "m29_len_tmp:\n  .zero 8\n" ++
  "bhfwh_number_buf:\n  .zero 8\n" ++
  "srpc_payload:\n  .zero 1024\n" ++
  -- bal_find_account_by_address private scratch:
  ".balign 8\n" ++
  "bfa_cnt:\n  .zero 8\n" ++
  "bfa_index:\n  .zero 8\n" ++
  "bfa_aoff:\n  .zero 8\n" ++
  "bfa_alen:\n  .zero 8\n" ++
  "bfa_doff:\n  .zero 8\n" ++
  "bfa_dlen:\n  .zero 8\n" ++
  "bfa_out_ptr:\n  .zero 8\n" ++
  "bfa_out_len:\n  .zero 8\n" ++
  "bfa_addr_hit:\n  .zero 20\n" ++
  "bfa_addr_miss:\n  .zero 20\n" ++
  -- coc3g.5 multi-hop: bal_same_block_delegation_code_resolve target-same-block-code
  -- fallback scratch (the single-hop target account record found in the BAL when the
  -- target's code is ALSO same-block-installed, not in the pre-state witness).
  ".balign 8\n" ++
  "bsbd_tgt_ptr:\n  .zero 8\n" ++
  "bsbd_tgt_len:\n  .zero 8\n" ++
  "bsbd_code_from_bal:\n  .zero 8\n" ++
  -- bal_recipient_storage_keys private scratch:
  ".balign 8\n" ++
  "brsk_off:\n  .zero 8\n" ++
  "brsk_len:\n  .zero 8\n" ++
  "brsk_cnt:\n  .zero 8\n" ++
  "brsk_eoff:\n  .zero 8\n" ++
  "brsk_elen:\n  .zero 8\n" ++
  "brsk_soff:\n  .zero 8\n" ++
  "brsk_slen:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "brsk_out:\n  .zero 256\n" ++
  -- .6.2.2.2.a: bal_txs_independent private scratch (the independence-guard
  -- walkers' cursors/counters; the probe's bti_bal_* fixtures are NOT needed in
  -- the verdict guest, only this scratch). All runtime-written before read.
  ".balign 8\n" ++
  "bti_acct_cnt:\n  .zero 8\n" ++
  "bti_aoff:\n  .zero 8\n" ++
  "bti_alen:\n  .zero 8\n" ++
  "bti_off:\n  .zero 8\n" ++
  "bti_len:\n  .zero 8\n" ++
  "bti_first_tx:\n  .zero 8\n" ++
  "bti_has_write:\n  .zero 8\n" ++
  "bti_conflict:\n  .zero 8\n" ++
  "bti_err:\n  .zero 8\n" ++
  "bti_rd_cnt:\n  .zero 8\n" ++
  "bti_t_cnt:\n  .zero 8\n" ++
  "bti_t_eoff:\n  .zero 8\n" ++
  "bti_t_elen:\n  .zero 8\n" ++
  "bti_t_foff:\n  .zero 8\n" ++
  "bti_t_flen:\n  .zero 8\n" ++
  "bti_sc_cnt:\n  .zero 8\n" ++
  "bti_sc_soff:\n  .zero 8\n" ++
  "bti_sc_slen:\n  .zero 8\n" ++
  "bti_sc_coff:\n  .zero 8\n" ++
  "bti_sc_clen:\n  .zero 8\n" ++
  -- .6.2.2.2.a: per-tx runtime-result arrays + context scratch for the gated
  -- multi-tx dispatch loop (.6.2.2.2.b). U64 arrays are cheap tx-indexed
  -- full-capacity arenas; the active loop gate remains bvMtxActiveTxCap until
  -- the sender-balance algorithm lands. bv_mtx_ctx is one 192-byte
  -- multi_tx_nth_context record reused per index.
  ".balign 8\n" ++
  "bv_mtx_gas_left:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_refund:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_calldata:\n  .zero " ++ toString bvMtxU64ArenaBytes ++ "\n" ++
  "bv_mtx_ctx:\n  .zero 192\n" ++
  -- bmvmx.5.5.6.3: scratch for the exact multi-tx nonce check. The
  -- running per-sender counts now live in bv_b1_sender_table after the
  -- pre-loop indexed sender aggregation.

  "bv_mtx_nonce_pre:\n  .zero 8\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2: cross-tx committed-storage table. After each per-tx dispatch
  -- the multi-tx loop upserts the live exec log's entries here, re-keyed (addrHash) to that
  -- tx's recipient (its entries are all the recipient's own because dispatch_tx_runtime_code
  -- requires self-contained), so the NEXT tx's preload can thread a prior tx's committed
  -- value via exec_log_latest_value. Capacity counts unique (recipient, slotKey) keys;
  -- duplicate writes update in place. The active chunked table keeps the same 128-entry
  -- page layout over four pages (512 unique keys total); unique-key overflow is
  -- conservative and surfaced via bv_mtx_committed_chunk_overflow. The legacy single-page
  -- labels remain while the stacked transition lands, but block-verdict call sites use the
  -- chunked count/table/overflow labels. dtrc_recipkey / dtrc_threadval are the per-slot
  -- query key and threaded-value output buffer.
  ".balign 8\n" ++
  "bv_mtx_committed_count:\n  .zero 8\n" ++
  "bv_mtx_committed_overflow:\n  .zero 8\n" ++
  "bv_mtx_committed_chunk_count:\n  .zero 8\n" ++
  "bv_mtx_committed_chunk_overflow:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_mtx_committed:\n  .zero " ++ toString bvMtxCommittedBytes ++ "\n" ++
  "bv_mtx_committed_chunked:\n  .zero " ++ toString bvMtxCommittedChunkBytes ++ "\n" ++
  "dtrc_recipkey:\n  .zero 32\n" ++
  "dtrc_threadval:\n  .zero 32\n" ++
  "dtrc_slotkey_le:\n  .zero 32\n" ++   -- ogjan: LE byte-reverse of bvcd_keys[i] for the exec_log_latest_value slotKey match
  -- coc3g.5: 20-byte EIP-7702 delegated TARGET address scratch. When the recipient's
  -- resolved code is a 0xef0100||target marker (a prior-block-delegated EOA), the
  -- dispatch follows the marker to the target's code while keeping env.ADDRESS = the
  -- delegating EOA (so SSTORE keys the EOA's storage, per interpreter.py message setup).
  ".balign 8\n" ++
  "dtrc_deleg_target:\n  .zero 32\n" ++
  "bsbd_deleg_target:\n  .zero 24\n" ++
  "dwp_al_off:\n  .zero 8\n" ++
  "dwp_al_len:\n  .zero 8\n" ++
  -- bmvmx.1.4.4: single-tx EOA settlement scalars precomputed before
  -- block_state_root (additive; no consumer yet -> verdict byte-identical).
  -- Consumed later by .4.1/.4.2 to build execution-derived sender/coinbase leaves.
  ".balign 8\n" ++
  "bmvmx_avail:\n  .zero 8\n" ++
  "eip7708_tl_typed_avail:\n  .zero 8\n" ++
  -- Receipts completeness shape for the enforcement tail:
  --   0 unknown/none
  --   1 legacy single-tx simple EOA
  --   2 typed single-tx simple EOA
  --   3 single-tx calldata contract dispatch complete
  --   4 multi-tx EOA dispatch complete
  --   5 multi-tx contract dispatch complete
  --   60 top-level creation unsupported
  --   61 runtime dispatch miss / non-self-contained
  --   62 other multi-tx unsupported bail
  -- `bv_receipts_enforce_enabled` is the stable gate bit consumed by
  -- BlockVerdictReceiptsTail; the older availability flags remain as
  -- compatibility/debug signals for the paths that originally introduced them.
  "bv_receipts_completeness_shape:\n  .zero 8\n" ++
  "bv_receipts_enforce_enabled:\n  .zero 8\n" ++
  -- Capture-only deposit dispatch deliberately leaves the receipt/gas arena
  -- unpublished; completeness means its per-tx log windows are authoritative.
  "bv_deposit_capture_only:\n  .zero 8\n" ++
  "bv_deposit_runtime_capture_complete:\n  .zero 8\n" ++
  "bmvmx_gas_used:\n  .zero 8\n" ++
  "bmvmx_txoff:\n  .zero 8\n" ++
  "bmvmx_ctx:\n  .zero 192\n" ++
  ".balign 32\n" ++
  "bmvmx_value:\n  .zero 32\n" ++
  "bmvmx_eff_gas_price:\n  .zero 32\n" ++
  "bmvmx_priority_fee:\n  .zero 32\n" ++
  "bmvmx_basefee_be:\n  .zero 32\n" ++
  -- bmvmx.1.4.1: execution-derived sender balance debit (gas_used*eff_gas_price + value),
  -- the sender's balance decrease for the supported single-tx EOA class.
  "bmvmx_gascost:\n  .zero 32\n" ++
  "bmvmx_sender_debit:\n  .zero 32\n" ++
  -- bmvmx.1.4.2: execution-derived coinbase fee credit (priority_fee_per_gas * gas_used).
  "bmvmx_coinbase_credit:\n  .zero 32\n" ++
  -- .6.2.2.2.b: multi-tx dispatch loop index cursor.
  "bv_mtx_i:\n  .zero 8\n" ++
  -- fhsxz.2.4.2.57.11.6.5: parent (PRE-state) header RLP ptr/len, stashed by
  -- block_verdict from its input frame (8(s0)/16(s0)). dispatch_tx_runtime_code's
  -- witness lookups (code/slot/balance_at_header_state_root) MUST use the PRE-state
  -- root (the witness is the parent's post-state = this block's pre-state proof),
  -- not sv_this_rlp (this block's POST-state header), else a recipient whose account
  -- changes within the block (e.g. an SSTORE contract) is unprovable -> false bail.
  ".balign 8\n" ++
  "sv_pre_rlp_ptr:\n  .zero 8\n" ++
  "sv_pre_rlp_len:\n  .zero 8\n" ++
  "bv_witness_state_ptr:\n  .zero 8\n" ++
  "bv_witness_state_len:\n  .zero 8\n" ++
  -- dtrc_use_pre_header is retained for older call sites that set/clear it, but runtime witness
  -- lookups now always use sv_pre_rlp_* (the parent/pre-state header). dtrc_hdr_ptr/len holds the
  -- header ptr+len resolved once at dispatch_tx_runtime_code entry and consumed by account/code/
  -- storage lookups.
  ".balign 8\n" ++
  "dtrc_use_pre_header:\n  .zero 8\n" ++
  "dtrc_hdr_ptr:\n  .zero 8\n" ++
  "dtrc_hdr_len:\n  .zero 8\n" ++
  -- coc3g.5 multi-hop: scratch for locating the type-4 authorization_list span.
  "dtrc_auth_off:\n  .zero 8\n" ++
  "dtrc_auth_len:\n  .zero 8\n" ++
  -- bmvmx.1.4.2 compare: validate the coinbase credit against the BAL (additive; match flag only).
  ".balign 8\n" ++
  "bmvmx_coinbase_addr:\n  .zero 20\n" ++
  ".balign 8\n" ++
  "bmvmx_acct:\n  .zero 104\n" ++
  "bmvmx_cb_acct_ptr:\n  .zero 8\n" ++
  "bmvmx_cb_acct_len:\n  .zero 8\n" ++
  "bmvmx_cb_bal_len:\n  .zero 8\n" ++
  "bmvmx_cb_nonce_len:\n  .zero 8\n" ++
  "bmvmx_coinbase_match:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bmvmx_cb_balbytes:\n  .zero 32\n" ++
  "bmvmx_cb_post:\n  .zero 32\n" ++
  "bmvmx_cb_expected:\n  .zero 32\n" ++
  "bmvmx_cb_nonce:\n  .zero 32\n" ++
  -- bmvmx.1.4.1 compare: sender address + match flag (reuses bmvmx_acct/bmvmx_cb_* scratch,
  -- which the sender compare runs through before the coinbase compare).
  ".balign 8\n" ++
  "bmvmx_sender_addr:\n  .zero 20\n" ++
  -- 3vc2p.1: scratch for the derived tx.sender staged into env CALLER/ORIGIN by
  -- stage_runtime_payload_code (contract-recipient path).
  ".balign 8\n" ++
  "srpc_sender_addr:\n  .zero 20\n" ++
  -- 3vc2p.2: effective_gas_price + priority-fee scratch for the env.gasPrice staging.
  ".balign 8\n" ++
  "gp_egp:\n  .zero 32\n" ++
  "gp_prio:\n  .zero 32\n" ++
  -- i3djw.3: skip-list for the all-accounts non-storage comparator (32B-strided
  -- {recipient, sender, coinbase} plus system addresses, pinned outside the exec log).
  ".balign 8\n" ++
  "i3djw_skip_list:\n  .zero 288\n" ++   -- coc3g.6.5: 3 {recipient,sender,coinbase} + 6 system addresses (9*32)
  -- bmvmx.5.5.1 (umbrella-A1): MULTI-TX skip-list for the all-accounts exec-vs-BAL
  -- comparators. A multi-tx block's gas/value-coupled accounts are {sender_i,
  -- recipient_i} for every tx i plus the shared {coinbase} and 6 system addresses -> up to 2N+7 entries
  -- (N = bv_tx_count <= bvMtxFullTxCap). The skip list has 2N+7
  -- entries, 32-byte-strided,
  -- address in the first 20 bytes (zero-padded). bv_mtx_skip_idx is the build-loop
  -- cursor (kept in memory so it survives the address_from_pubkey/multi_tx_nth_context
  -- calls); bv_mtx_skip_ctx is the scratch record for re-extracting each recipient.
  ".balign 8\n" ++
  "bv_mtx_skip_list:\n  .zero " ++ toString bvMtxSkipListBytes ++ "\n" ++
  "bv_mtx_skip_count:\n  .zero 8\n" ++
  "bv_mtx_skip_idx:\n  .zero 8\n" ++
  "bv_mtx_skip_ctx:\n  .zero 192\n" ++
  -- EIP-8037 current-state aliveness for the multi-tx EOA shortcut.
  -- top-level value transfers pay NEW_ACCOUNT state gas only when the recipient
  -- is not alive in the transaction's current state. The header-state lookup is
  -- not enough after an earlier tx in the same block creates/funds that recipient,
  -- so the shortcut records recipients whose NEW_ACCOUNT charge has already been
  -- paid and suppresses repeats. 32-byte stride, 20-byte BE address prefix.
  ".balign 8\n" ++
  "bv_mtx_created_recipient_count:\n  .zero 8\n" ++
  "bv_mtx_created_recipient_table:\n  .zero " ++ toString bvMtxCreatedRecipientBytes ++ "\n" ++
  -- bmvmx.5.5.1 (umbrella-A2a): per-account aggregation of exec_nonstorage_effect_log
  -- for the multi-tx nonstorage comparators. record_nonstorage_effect APPENDS one record
  -- per CALL, so a multi-tx-touched account has N records; fold them into one entry keyed
  -- by the 20B BE address (first-seen pre kept, last-seen post overwritten) so the per-
  -- account comparator sees the block-aggregate {pre, post}. Dedup -> count <= the log cap,
  -- so cap x 112 B suffices. Interpolated as nonstorageEffectLogCap * 112 (NonstorageEffectLog.lean):
  -- the .Lbv_agg_append / nonstorage_effect_aggregate path has no separate bounds check, so an
  -- undersized buffer is a heap overflow; tying it to the cap keeps it correct as the cap is lifted.
  ".balign 8\n" ++
  "exec_nonstorage_effect_agg_count:\n  .zero 8\n" ++
  "exec_nonstorage_effect_agg:\n  .zero " ++ toString (nonstorageEffectLogCap * 112) ++ "\n" ++
  -- fva3w: pre-tx snapshots of the exec effect logs. A top-level tx that REVERTS or
  -- exceptionally aborts discards ALL its state changes (the spec rolls them back), so the
  -- value-transfer / CREATE non-storage + code effects recorded during it must be discarded
  -- too. Child frames already roll back via frame_return; but a top-level abort (INVALID /
  -- REVERT / OOG at depth 0) takes .exit_*_top with NO frame_return -> the effects survived,
  -- and the all-accounts non-storage comparator then saw a value change the BAL (correctly,
  -- net-zero) omitted -> bv_fail=44 (bal_aborted_account_access invalid/revert-call/callcode).
  -- Snapshot before the tx runtime dispatch; truncate back to it when the tx errored (status 0).
  ".balign 8\n" ++
  "bv_tx_effect_snap_ns_count:\n  .zero 8\n" ++
  "bv_tx_effect_snap_ns_overflow:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_count:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_next:\n  .zero 8\n" ++
  "bv_tx_effect_snap_code_overflow:\n  .zero 8\n" ++
  "bv_tx_effect_snap_storage_count:\n  .zero 8\n" ++   -- bbow4.2: storage exec-log count (evm_env+448) snapshot for tx-error truncation
  -- bmvmx.5.5.2 (umbrella-B1): scratch for the multi-tx per-sender FINAL-nonce check
  -- (BAL sender post nonce == pre + total sender tx count). bv_b1_finals is the 88-byte
  -- bal_account_nonstorage_finals output (separate from c2nsc_finals, which A2a's
  -- comparator uses); bv_b1_acct_ptr/len receive the sender's BAL AccountChanges.
  -- bv_b1_sender_table is sized to bvMtxSenderCountEntries distinct senders, which
  -- follows the full 200M tx-count target. Each row is a 32-byte padded address
  -- plus u64 total tx count, filled by b1_sender_count_table.
  ".balign 8\n" ++
  b1SenderCountTableScratchDataSection ++
  ".balign 8\n" ++
  "bv_b1_sender_count:\n  .zero 8\n" ++
  "bv_b1_sender_table:\n  .zero " ++ toString bvMtxSenderCountTableBytes ++ "\n" ++
  "bv_b1_count:\n  .zero 8\n" ++
  "bv_b1_expected:\n  .zero 8\n" ++
  "bv_b1_acct_ptr:\n  .zero 8\n" ++
  "bv_b1_acct_len:\n  .zero 8\n" ++
  "bv_b1_finals:\n  .zero 88\n" ++
  -- bmvmx.5.5.2.2.2 (B2.2): per-sender running balance table for multi-tx sender debits.
  -- Entries are 64B: sender address lane (first 20B used) + running u256 BE balance.
  -- Capacity follows bvMtxActiveTxCap so all-distinct current-fixture blocks do
  -- not hit the old 16-entry table-full path. Full 9523-tx aggregation is a
  -- separate follow-up slice.
  "bv_b2_count:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_b2_table:\n  .zero " ++ toString bvMtxSenderBalanceTableBytes ++ "\n" ++
  "bv_b2_debit_out:\n  .zero 48\n" ++
  -- B2.3 typed-tx fee scratch (bmvmx.5.5.2.2.6): the B2.2 loop adds
  -- type-3 blob-data-gas sender-debit terms; type-4 auth gas is already in
  -- bvgr_receipt_gas_increments. txtype/innoff come from tx_type_dispatch;
  -- blobcount = blob hashes; feedebit is the u256 fee accumulator added into
  -- the sender debit.
  "bv_b23_txtype:\n  .zero 8\n" ++
  "bv_b23_innoff:\n  .zero 8\n" ++
  "bv_b23_blobcount:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_b23_feedebit:\n  .zero 32\n" ++
  "mtxsd_gascost:\n  .zero 32\n" ++
  -- i3djw.3: scratch for bal_all_accounts_nonstorage_consistent + its per-account deps
  -- (bal_account_nonstorage_consistent / _finals). rfu_* is already linked (other rlp users).
  ".balign 8\n" ++
  "c3ns_acct_count:\n  .zero 8\n" ++
  "c3ns_acct_off:\n  .zero 8\n" ++
  "c3ns_acct_len:\n  .zero 8\n" ++
  "c3ns_addr_off:\n  .zero 8\n" ++
  "c3ns_addr_len:\n  .zero 8\n" ++
  "c2nsc_finals:\n  .zero 88\n" ++
  "c2nsf_off:\n  .zero 8\n" ++
  "c2nsf_len:\n  .zero 8\n" ++
  "c2nsf_cnt:\n  .zero 8\n" ++
  "c2nsf_toff:\n  .zero 8\n" ++
  "c2nsf_tlen:\n  .zero 8\n" ++
  "c2nsf_coff:\n  .zero 8\n" ++
  "c2nsf_clen:\n  .zero 8\n" ++
  -- i3djw.3 reverse: scratch for bal_all_accounts_nonstorage_covers.
  "c3cov_acct_count:\n  .zero 8\n" ++
  "c3cov_acct_off:\n  .zero 8\n" ++
  "c3cov_acct_len:\n  .zero 8\n" ++
  "c3cov_addr_off:\n  .zero 8\n" ++
  "c3cov_addr_len:\n  .zero 8\n" ++
  -- bmvmx.5.5.7.3 step c: matched-bitmap for the LINEARIZED bal_all_accounts_nonstorage_covers
  -- (1 byte per agg entry, indexed by agg index). MUST be >= nonstorageEffectLogCap bytes.
  "c3cov_covered:\n  .zero " ++ toString nonstorageEffectLogCap ++ "\n" ++
  -- i3djw.4: scratch for bal_all_accounts_code_consistent (FORWARD per-account CODE compare,
  -- with the EIP-7702 delegation skip). bacc_finals is the per-account 88-byte finals scratch
  -- consumed by bal_account_code_consistent; baac_* are the account-iteration scratch. The
  -- c2nsf_*/rfu_* scratch the inlined finals helper needs is already provided just above.
  ".balign 8\n" ++
  "baac_acct_count:\n  .zero 8\n" ++
  "baac_acct_off:\n  .zero 8\n" ++
  "baac_acct_len:\n  .zero 8\n" ++
  "baac_addr_off:\n  .zero 8\n" ++
  "baac_addr_len:\n  .zero 8\n" ++
  "bacc_finals:\n  .zero 88\n" ++
  -- yisv8.1: recipient self-balance scratch for the env.SELFBALANCE (word 1) staging.
  ".balign 32\n" ++
  "yisv8_self_bal:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bmvmx_sender_match:\n  .zero 8\n" ++
  -- bmvmx.1.4.3.1: envelope predicate scratch. bmvmx_sender_checked / bmvmx_coinbase_checked
  -- mark that the exec-derived balance compare was PERFORMED in the cheap envelope (single-tx
  -- + legacy) with the relevant addresses distinct (sender!=recipient/coinbase for the sender
  -- compare; coinbase!=sender/recipient for the coinbase compare). .4.3.2 completes the
  -- envelope with the deferred EOA-recipient check and then gates the verdict reject on
  -- (avail && checked && EOA && !match), without false-rejecting skipped / out-of-envelope /
  -- overlapping blocks.
  ".balign 8\n" ++
  "bmvmx_sender_checked:\n  .zero 8\n" ++
  "bmvmx_coinbase_checked:\n  .zero 8\n" ++
  -- bmvmx.1.6.3 (balance slice): scratch for the execution-derived sender balance compare
  -- (tx_gas_bal_post_verify_runtime + sender_debit_from_gas). tea_*/u256m_acc/tgsbl_*/bpf_*/
  -- tefgp_* are already provided by the EOA tx_gas_bal_post_verify path; only sdfg_gascost
  -- (sender_debit) and the tgbpvr_* / output buffer are new.
  ".balign 32\n" ++
  "sdfg_gascost:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_in:\n  .zero 32\n" ++
  ".balign 32\n" ++
  "tgbpvr_pre:\n  .zero 32\n" ++
  "tgbpvr_post:\n  .zero 32\n" ++
  "tgbpvr_egp:\n  .zero 32\n" ++
  "tgbpvr_prio:\n  .zero 32\n" ++
  "tgbpvr_value:\n  .zero 32\n" ++
  "tgbpvr_gasdebit:\n  .zero 32\n" ++
  "tgbpvr_expected:\n  .zero 32\n" ++
  "tgbpvr_zero:\n  .zero 32\n" ++
  "tgbpvr_blobdebit:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "tgbpvr_to:\n  .zero 24\n" ++
  "tgbpvr_iscreation:\n  .zero 8\n" ++
  "tgbpvr_tx_type:\n  .zero 8\n" ++
  "tgbpvr_inner_off:\n  .zero 8\n" ++
  "tgbpvr_blob_count:\n  .zero 8\n" ++
  "tgbpvr_lookup:\n  .zero 168\n" ++
  ".balign 8\n" ++
  "bv_sender_bal_check:\n  .zero 192\n" ++
  -- bmvmx.2: scratch for the check_transaction upfront-balance pre-validation
  -- (sender_pre_balance >= gas_limit*max_fee_per_gas + blob_gas*max_fee_per_blob_gas
  -- + tx.value). bv_upfront_cost holds the cumulative upfront cost; bv_upfront_islt
  -- is the u256_lt_be verdict (1 iff pre_balance < upfront -> reject).
  ".balign 8\n" ++
  "bv_upfront_cost:\n  .zero 32\n" ++
  "bv_upfront_blob_cost:\n  .zero 32\n" ++
  "bv_upfront_blob_count:\n  .zero 8\n" ++
  "bv_upfront_islt:\n  .zero 8\n" ++
  -- bmvmx.5: out scratch for the hoisted single-tx fee-validity gate's
  -- tx_effective_gas_pricing call (effective_gas_price / priority_fee_per_gas, 32B BE
  -- each). Only the call's status (2/3) is consumed; the values are unused here.
  ".balign 8\n" ++
  "bv_fee_egp_scratch:\n  .zero 32\n" ++
  "bv_fee_prio_scratch:\n  .zero 32\n" ++
  -- bmvmx.5: block base_fee (BE, 32B) for the multi-tx fee gate -- multi_tx_nth_context does
  -- not fill the record's base_fee, so the mtx loop reverses the payload LE base_fee here once.
  "bv_mtx_base_fee_be:\n  .zero 32\n" ++
  -- Live coinbase fee effect scratch for multi-tx BALANCE(COINBASE) reads.
  ".balign 8\n" ++
  "bv_mtx_cbfee_receipt_inc:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "bv_mtx_cbfee_egp:\n  .zero 32\n" ++
  "bv_mtx_cbfee_priority:\n  .zero 32\n" ++
  "bv_mtx_cbfee_credit:\n  .zero 32\n" ++
  "bv_mtx_cbfee_pre:\n  .zero 32\n" ++
  "bv_mtx_cbfee_post:\n  .zero 32\n" ++
  -- bmvmx.5: per-mtx-tx sender scratch for the multi-tx nonce lower-bound check. sender address
  -- (address_from_pubkey of the verified public_keys[i]) + the sender's pre-state account
  -- (account_at_header_state_root output; nonce@0).
  "bv_mtx_sender_addr:\n  .zero 32\n" ++
  "bv_mtx_sender_acct:\n  .zero 128\n" ++
  -- bmvmx.5: single-tx contract-recipient sender scratch (same role as the mtx pair, i=0 path).
  "bv_stx_sender_addr:\n  .zero 32\n" ++
  "bv_stx_sender_acct:\n  .zero 128\n" ++
  -- bmvmx.1.6.6: scratch for the all-accounts per-slot tuple-sequence check (#8606). batsc_* is
  -- the wrapper's own scratch; the sub-helpers' scratch (atsc_*/bts_*/els_*) come from their Data
  -- defs. rfu_* (rlp_field_to_u64) is already provided above; slot_tuple_sequences_match is
  -- self-contained.
  ".balign 8\n" ++
  "batsc_acct_count:\n  .zero 8\n" ++
  "batsc_acct_off:\n  .zero 8\n" ++
  "batsc_acct_len:\n  .zero 8\n" ++
  "batsc_addr_off:\n  .zero 8\n" ++
  "batsc_addr_len:\n  .zero 8\n" ++
  ".balign 32\n" ++
  "batsc_key:\n  .zero 32\n" ++ "\n" ++
  accountTupleSequencesConsistentData ++ "\n" ++
  balSlotTupleSequenceData ++ "\n" ++
  execLogSlotTuplesData ++ "\n" ++
  -- Keep the large authorization replay table last so growing it cannot move
  -- any established data symbol or arena anchor.
  ".balign 8\n" ++
  "teer_success_count:\n  .zero 8\n" ++
  "teer_success_table:\n  .zero 33920\n"

end EvmAsm.Codegen
