/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptsTail

  Tail of block_verdict (post-gas-result gate: EIP-7702 nonce-reuse guard +
  receipts-consensus enforcement + epilogue), split out of BlockVerdictFunction.lean
  to stay under the 1500-line file cap (bmvmx.9). Pure asm-string fragment,
  concatenated back byte-identically via blockVerdictReceiptsTail.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

/-- Tail of `block_verdict`, concatenated after the main body (byte-identical). -/
def blockVerdictReceiptsTail : String :=
  ".Lbv_after_gas_result_gate:\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  mv a1, s3\n" ++
  "  la t2, bv_bal_start; ld a2, 0(t2)\n" ++
  "  la t2, bv_bal_len; ld a3, 0(t2)\n" ++
  "  jal ra, eip7702_nonce_reuse_guard\n" ++
  "  bnez a0, .Lbv_eip7702_nonce_reuse_fail\n" ++
  "  la t2, bvgr_arena_status; ld t2, 0(t2); bnez t2, .Lbv_receipts_no_runtime_gas\n" ++
  -- .63.1.6.2.8: the materialized receipt's cumulative_gas must include the EIP-7623 calldata
  -- floor. block_verdict_gas_result_arena_prepare set bvgr_receipt_gas_increments[tx] =
  -- max(after_refund, bvgr_calldata_floor), but the dispatcher's bvgr_calldata_floor is 0 for
  -- EOA value-transfer txs, so a legacy transfer WITH calldata under-charged the receipt -> a
  -- spurious receipts-root mismatch (latent false-reject). The block-gas gate above
  -- (block_verdict_tx_state_gas_array) already computed the SOUND per-tx EIP-7623 floor into
  -- bsg_floor_gas using its own safe calldata source; redo the max with it. max(after_refund,
  -- floor) is exactly the spec receipt increment (amsterdam Account.lean:1062-1064), so this
  -- never over-charges. SINGLE-TX ONLY: for multi-tx bsg_floor_gas is the last tx's floor, not
  -- tx0's. bsg_floor_gas is written only by the gas gate; for single-tx it is either tx0's floor
  -- or 0 (gate bailed before computing it) -- both safe under max. No calldata re-iteration here,
  -- so no out-of-bounds read on max-calldata rows.
  "  la t4, bvgr_arena_tx_count; ld t4, 0(t4); li t5, 1; bne t4, t5, .Lbv_st_receipt_floor_skip\n" ++
  "  la t0, bvgr_receipt_gas_increments; ld t1, 0(t0)\n" ++
  "  la t2, bsg_floor_gas; ld t3, 0(t2)\n" ++
  "  bgeu t1, t3, .Lbv_st_receipt_floor_skip\n" ++
  "  sd t3, 0(t0)\n" ++
  ".Lbv_st_receipt_floor_skip:\n" ++
  "  la t2, bv_tx_list_ptr; ld a0, 0(t2)\n" ++
  "  la t2, bv_tx_list_len; ld a1, 0(t2)\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bvgr_receipt_gas_increments\n" ++
  "  la a4, bvgr_tx_total_state_gas\n" ++
  "  la a5, bvgr_block_gas_increments\n" ++
  "  la a6, bvgr_tx_exec_state_gas\n" ++
  "  jal ra, block_verdict_receipt_gas_eip8037_adjust\n" ++
  -- EIP-7702 SELFDESTRUCT delegated-code rows expose one more receipt-only
  -- regular-gas correction after the generic type-4 adjustment above. The
  -- exact block gas check is already governed by the EIP-8037 state dimension
  -- for this shape, but receipts in execution-specs use tx_gas_used_after_refund
  -- and include the executed SELFDESTRUCT regular path. Keep this narrow:
  -- single tx, type-4, and the runtime SELFDESTRUCT staging flag set by the
  -- handler, not mere bytecode containment.
  "  la t2, bvgr_arena_tx_count; ld t2, 0(t2); li t3, 1; bne t2, t3, .Lbv_receipt_sd_skip\n" ++
  "  la t2, bv_simple_transfer_tx; ld t2, 160(t2); li t3, 4; bne t2, t3, .Lbv_receipt_sd_skip\n" ++
  "  la t0, evm_selfdestruct_staged; ld t0, 0(t0); beqz t0, .Lbv_receipt_sd_skip\n" ++
  "  la t4, bvgr_receipt_gas_increments; ld t5, 0(t4); li t6, 32690; add t5, t5, t6; sd t5, 0(t4); j .Lbv_receipt_sd_skip\n" ++
  ".Lbv_receipt_sd_skip:\n" ++
  "  la t2, bvgr_arena_tx_count; ld t2, 0(t2); li t3, 1; bne t2, t3, .Lbv_receipt_ecc_skip\n" ++
  "  la t2, bv_simple_transfer_tx; ld t2, 160(t2); li t3, 4; bne t2, t3, .Lbv_receipt_ecc_skip\n" ++
  "  la t0, ecc_same_block_hit; ld t0, 0(t0); beqz t0, .Lbv_receipt_ecc_skip\n" ++
  "  la t4, bvgr_receipt_gas_increments; ld t5, 0(t4); li t6, 32690; add t5, t5, t6; sd t5, 0(t4)\n" ++
  ".Lbv_receipt_ecc_skip:\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  la a1, bvgr_receipt_gas_increments\n" ++
  "  la t2, bvgr_arena_tx_count; ld a2, 0(t2)\n" ++
  "  la a3, bv_tx_status_arr\n" ++   -- .63.1.6.2.1: per-tx settle success bits
  "  la a4, bv_tx_log_window\n" ++   -- .63.1.6.2.1: per-tx block-arena log windows
  "  jal ra, block_receipt_records_materialize\n" ++
  "  la t2, brr_status; ld t2, 0(t2); bnez t2, .Lbv_receipt_records_fail\n" ++
  -- .63.1.6.2.1: encode per-record logs RLP + bloom and fill logs_desc_ptr.
  "  la a0, brr_control\n" ++
  "  jal ra, block_receipt_logs_materialize\n" ++
  "  la t2, bv_receipt_logs_status; sd a0, 0(t2)\n" ++
  -- Persist the exact log-materializer status before branching:
  -- 0 success, 1 malformed log window or RLP encode failure, 2 bloom helper failure,
  -- 3 block-log arena/capture overflow. For enforced receipt shapes, statuses 1/2
  -- are malformed supported data and reject; status 3 remains capacity debt and
  -- conservatively accepts.
  -- .63.1.6.2.3 (slice B): TX-BEARING receipts-consensus enforcement. execution-specs
  -- apply_body recomputes receipt_root = root(receipts_trie) and block_logs_bloom and hard-
  -- rejects on a header mismatch (fork.py 368-371). Encode the materialized per-tx receipt
  -- records (status||cumulative_gas||bloom||logs, with the .2.1 log descriptors @56) into one
  -- RLP list, then validate header.receipts_root == MPT(indexed(receipts)) AND header.bloom ==
  -- OR(receipt blooms) via the shared consensus validator. Unsupported capacity still
  -- conservatively accepts, but malformed helper statuses on an enforced receipt shape reject
  -- instead of silently accepting. Confirmed root/bloom mismatches reject as before.
  "  bnez a0, .Lbv_receipt_logs_helper_status\n" ++
  -- `bv_block_log_overflow` is recorded separately from the helper return status because
  -- block_log_window_snapshot can set it before this tail runs. Overflow remains capacity
  -- debt and never becomes a reject without EEST/spec coverage evidence.
  "  la t2, bv_block_log_overflow; ld t2, 0(t2); bnez t2, .Lbv_receipts_accept\n" ++
  -- 8uld3.4: derive EIP-6110 deposit requests from EXECUTION-produced logs and
  -- verify the final requests_hash against the value that the early header-hash
  -- check already committed to (`erh_requests_hash`). This stops trusting the
  -- SSZ execution_requests.deposits body: a block whose SSZ deposits match the
  -- header but whose receipts contain different deposit logs is rejected here.
  -- The scratch sizes mirror the named block-log and request-body arenas;
  -- over-capacity remains conservative and is tracked by follow-up capacity beads.
  "  la a0, bv_block_log_descs\n" ++
  "  la t2, bv_block_log_count; ld a1, 0(t2)\n" ++
  "  la a2, bv_block_log_data\n" ++
  "  la a3, bv_block_log_meta\n" ++
  "  la a4, c1_log_records\n" ++
  "  jal ra, materialize_log_records\n" ++
  "  la a0, c1_log_records\n" ++
  "  la t2, bv_block_log_count; ld a1, 0(t2)\n" ++
  "  la a2, c1_dbody\n" ++
  "  la a3, c1_dstatus\n" ++
  "  jal ra, parse_deposit_requests\n" ++
  "  la t2, c1_dlen; sd a0, 0(t2)\n" ++
  "  la t2, c1_dstatus; ld t2, 0(t2); bnez t2, .Lbv_requests_hash_fail\n" ++
  "  la a0, c1_dbody; la t2, c1_dlen; ld a1, 0(t2)\n" ++
  "  la a2, dbsr_wbody; la t2, dbsr_wlen; ld a3, 0(t2)\n" ++
  "  la a4, dbsr_cbody; la t2, dbsr_clen; ld a5, 0(t2)\n" ++
  "  add t0, a1, a3; add t0, t0, a5; addi t0, t0, 12\n" ++
  "  li t2, " ++ toString bvMaxExecutionRequestSectionBytes ++ "; bgtu t0, t2, .Lbv_requests_hash_fail\n" ++
  "  la t1, c1_er_assembled_len; sd t0, 0(t1)\n" ++
  "  la a6, erh_requests_hash\n" ++
  "  la a7, c1_er_assembled\n" ++
  "  jal ra, requests_hash_verify\n" ++
  "  la t2, c1_erh_status; sd a0, 0(t2)\n" ++
  "  bnez a0, .Lbv_requests_hash_fail\n" ++
  -- CONSERVATIVE COMPLETENESS GATE: enforce only when the transaction-shape-specific
  -- receipt completeness classifier set bv_receipts_enforce_enabled. The classifier keeps
  -- legacy simple EOA, typed simple EOA, single-tx contract, multi-tx EOA/contract,
  -- top-level creation unsupported, and dispatch-miss/non-self-contained reasons separate
  -- in bv_receipts_completeness_shape so unsupported materialization cannot be confused with
  -- a consensus comparison that is safe to enforce.
  "  la t2, bv_receipts_enforce_enabled; ld t2, 0(t2); beqz t2, .Lbv_receipts_accept\n" ++
  ".Lbv_receipts_enforce:\n" ++
  "  la a0, brr_control; la a1, bv_receipts_rlp; li a2, " ++ toString bvReceiptsRlpBytes ++ "; la a3, bv_receipts_rlp_len\n" ++
  "  jal ra, receipt_records_encode_no_logs\n" ++
  -- Persist the exact encoder status before branching: 0 success,
  -- 1 malformed arena, 2 missing logs descriptor, 3 output/scratch overflow,
  -- 4 unsupported tx type, 5 record-count capacity overflow. Statuses 3/5 remain
  -- capacity debt; statuses 1/2/4 are malformed enforced-shape data and reject.
  "  la t2, bv_receipts_encoder_status; sd a0, 0(t2)\n" ++
  "  bnez a0, .Lbv_receipts_encoder_helper_status\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_receipts_rlp; la t0, bv_receipts_rlp_len; ld a3, 0(t0)\n" ++
  "  jal ra, block_validate_receipts_consensus_list\n" ++
  -- Persist the exact validator status before branching: 0 success, 1 receipts-root helper
  -- failure, 2 root mismatch, 3 logs-bloom helper failure, 4 bloom mismatch. In an
  -- enforced shape, helper statuses mean the supported receipt list could not be
  -- checked precisely, so reject instead of silently accepting.
  "  la t2, bv_receipts_validator_status; sd a0, 0(t2)\n" ++
  "  li t0, 2; beq a0, t0, .Lbv_receipts_root_mismatch\n" ++
  "  li t0, 4; beq a0, t0, .Lbv_receipts_bloom_mismatch\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_receipts_helper_fail\n" ++
  "  li t0, 3; beq a0, t0, .Lbv_receipts_helper_fail\n" ++
  "  j .Lbv_receipts_accept\n" ++
  ".Lbv_receipt_logs_helper_status:\n" ++
  "  li t0, 3; beq a0, t0, .Lbv_receipts_accept\n" ++
  "  la t0, bv_receipts_enforce_enabled; ld t0, 0(t0); beqz t0, .Lbv_receipts_accept\n" ++
  "  j .Lbv_receipts_helper_fail\n" ++
  ".Lbv_receipts_encoder_helper_status:\n" ++
  "  li t0, 3; beq a0, t0, .Lbv_receipts_accept\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_receipts_accept\n" ++
  "  j .Lbv_receipts_helper_fail\n" ++
  ".Lbv_receipts_accept:\n" ++
  "  li a0, 1; j .Lbv_ret\n" ++
  ".Lbv_receipts_no_runtime_gas:\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
  "  li a1, 0\n" ++
  "  li a2, 0\n" ++
  "  li a3, 0\n" ++
  "  li a4, 0\n" ++
  "  jal ra, block_receipt_records_materialize\n" ++
  "  li a0, 1; j .Lbv_ret\n" ++
  ".Lbv_cmp_mismatch:\n" ++
  "  li t0, 1; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_header_fail:\n" ++
  "  li t0, 2; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_state_fail:\n" ++
  "  li t0, 3; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_no_bal_for_tx:\n" ++
  "  li t0, 4; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_zero_gas_used:\n" ++
  "  li t0, 5; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_notx_gas_used_fail:\n" ++   -- wsvlq: no-tx block with nonzero header.gas_used
  "  li t0, 13; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_public_keys_fail:\n" ++
  "  li t0, 6; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_public_keys_sender_fail:\n" ++   -- bmvmx.3.2: a witness public_keys[i] != recovered tx[i] signer (or recovery failed)
  "  li t0, 52; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_gas_fail:\n" ++
  "  li t0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_code_preimage_fail:\n" ++
  "  li t0, 11; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_parse_fail:\n" ++
  "  li t0, 12; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_limit_fail:\n" ++
  "  li t0, 13; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip8037_gas_fail:\n" ++
  "  addi t0, a0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7702_nonce_reuse_fail:\n" ++
  "  li t0, 14; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_blockhash_headers_fail:\n" ++
  "  li t0, 15; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_empty_tx_fail:\n" ++
  "  li t0, 16; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_tx_gas_precharge_fail:\n" ++
  "  li t0, 17; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_simple_transfer_recipient_fail:\n" ++
  "  li t0, 28; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_simple_transfer_fee_recipient_fail:\n" ++
  "  li t0, 29; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7778_block_gas_fail:\n" ++
  "  li t0, 19; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipt_records_fail:\n" ++
  "  li t0, 25; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_requests_hash_fail:\n" ++
  "  li t0, 55; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipts_helper_fail:\n" ++     -- enforced receipt helper failure on supported shape
  "  li t0, 56; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_notx_receipts_root_fail:\n" ++   -- .63.1.6.2.3: no-tx header.receipts_root != empty-trie root
  "  li t0, 50; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_notx_bloom_fail:\n" ++           -- .63.1.6.2.3: no-tx header.bloom != 256 zero bytes
  "  li t0, 51; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipts_root_mismatch:\n" ++     -- .63.1.6.2.3 (slice B): tx-bearing header.receipts_root mismatch
  "  li t0, 53; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_receipts_bloom_mismatch:\n" ++    -- .63.1.6.2.3 (slice B): tx-bearing header.logs_bloom mismatch
  "  li t0, 54; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_versioned_hashes_fail:\n" ++
  "  li t0, 27; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_withdrawals_root_fail:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_blob_gas_used_fail:\n" ++
  "  li t0, 33; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_state_gas_fail:\n" ++   -- g8zeq.1.4.2: header.gas_used < block_state_gas floor
  "  li t0, 35; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_gas_used_over_fail:\n" ++   -- g8zeq.1.4.2: header.gas_used > max(block_regular, block_state) (over-claim)
  "  li t0, 41; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_mtx_recipient_unresolvable_fail:\n" ++   -- fhsxz.2.4.2.57.11.6.5.4 (e): mtx tx recipient unresolvable at pre-state root (incomplete witness)
  "  li t0, 47; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_hash_mismatch:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_storage_mismatch_fail:\n" ++   -- bmvmx.1.6.2: recipient BAL storage != execution
  "  li t0, 34; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_recipient_field_fail:\n" ++    -- bmvmx.1.6.3: recipient BAL nonce/code claims a change execution didn't make
  "  li t0, 35; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_storage_omit_fail:\n" ++       -- bmvmx.1.6.5: recipient BAL omits a storage change execution made
  "  li t0, 36; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_allaccounts_fail:\n" ++        -- bmvmx.1.6.4.3: a non-recipient BAL account's storage != execution
  "  li t0, 37; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_reads_fail:\n" ++              -- bmvmx.1.6.7: recipient BAL storage_read slot never accessed in execution
  "  li t0, 38; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_sender_bal_fail:\n" ++             -- bmvmx.1.6.3: BAL sender post balance != execution-derived (pre - gas_charge - value)
  "  li t0, 39; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_sender_nonce_fail:\n" ++           -- bmvmx.1.6.3: BAL sender post nonce != pre_nonce + 1 (execution increments once)
  "  li t0, 40; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_recipient_bal_fail:\n" ++          -- bmvmx.1.6.3: BAL contract-recipient post balance != recipient_pre + tx.value
  "  li t0, 41; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_tuple_fail:\n" ++              -- bmvmx.1.6.6: a non-recipient account's per-slot (block_access_index,value) tuple sequence != exec
  "  li t0, 42; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_code_covers_fail:\n" ++        -- i3djw: execution deployed/cleared code for an account the BAL omits (hidden created/destroyed account)
  "  li t0, 43; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_nonstorage_fail:\n" ++         -- i3djw.3: a non-recipient BAL account's declared balance/nonce change != exec non-storage effect
  "  li t0, 44; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_nonstorage_covers_fail:\n" ++  -- i3djw.3 reverse: exec net-changed an account's balance/nonce that the BAL omits
  "  li t0, 45; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_code_consistent_fail:\n" ++    -- i3djw.4: a BAL account's declared code change != exec code-effect (and not a 7702 delegation)
  "  li t0, 46; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_sender_upfront_fail:\n" ++         -- bmvmx.2: sender_pre_balance < gas_limit*max_fee + value (InsufficientBalanceError)
  "  li t0, 48; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_fee_invalid_fail:\n" ++           -- bmvmx.4: tx fee invalid (max_fee < base_fee, or priority > max_fee) -> check_transaction reject
  "  li t0, 49; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lbv_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
