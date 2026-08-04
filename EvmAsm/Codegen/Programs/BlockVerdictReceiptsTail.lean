/-
  EvmAsm.Codegen.Programs.BlockVerdictReceiptsTail

  Tail of block_verdict (post-gas-result gate: EIP-7702 nonce-reuse guard +
  receipts-consensus enforcement + epilogue), split out of BlockVerdictFunction.lean
  to stay under the 1500-line file cap (bmvmx.9). Pure asm-string fragment,
  concatenated back via blockVerdictReceiptsTail. Targeted pre-materialization
  receipt repair fragments were removed so wrong upstream values fail here.
-/

import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictDepositFallback

namespace EvmAsm.Codegen

/-- Tail of `block_verdict`, concatenated after the main body.
    Targeted pre-materialization receipt normalizations are intentionally absent:
    gas/status/log values must be derived from the verdict-side execution data
    before the consensus checks. -/
def blockVerdictReceiptsTail : String :=
  ".Lbv_after_gas_result_gate:\n" ++
  "  la t0, bv_tx_count; ld t0, 0(t0); li t1, 2; bltu t0, t1, .Lbv_mtx_b2_return\n" ++
  "  la t0, bvgr_arena_status; ld t0, 0(t0); bnez t0, .Lbv_mtx_b2_return\n" ++
  "  j .Lbv_b2_entry\n" ++
  ".Lbv_mtx_b2_return:\n" ++
  "  # GH #11410: dynamic witness-code-preimage gate. Every code read execution\n" ++
  "  # actually performed (the guest's tracked get_code, code_read_fetch) must\n"  ++
  "  # resolve to a keccak-verified preimage in witness.codes; spec raises on a\n"  ++
  "  # missing preimage at read time (state_tracker.py:269-270, witness_state.py:204-212).\n" ++
  "  addi sp, sp, -64; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  la t0, code_reads_overflow; ld t0, 0(t0); bnez t0, .Lbv_cpg_fail\n" ++
  "  la t0, code_reads_count; ld s0, 0(t0)\n" ++
  "  li s1, 0xa1d20000\n" ++
  ".Lbv_cpg_loop:\n" ++
  "  beqz s0, .Lbv_cpg_done\n" ++
  "  la a0, svf_codes_ptr; ld a0, 0(a0)\n" ++
  "  la a1, svf_codes_len; ld a1, 0(a1)\n" ++
  "  addi a2, s1, 32; addi a3, sp, 32; addi a4, sp, 40\n" ++
  "  jal ra, witness_codes_lookup_by_hash\n" ++
  "  bnez a0, .Lbv_cpg_fail\n" ++
  "  addi s1, s1, 64; addi s0, s0, -1; j .Lbv_cpg_loop\n" ++
  ".Lbv_cpg_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 64\n" ++
  "  j .Lbv_cpg_past\n" ++
  ".Lbv_cpg_fail:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 64\n" ++
  "  j .Lbv_code_preimage_fail\n" ++
  ".Lbv_cpg_past:\n" ++
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
  -- are malformed supported data and reject. A separately recorded block-log overflow
  -- rejects below before derived-deposit requests_hash verification, since a hidden
  -- deposit log would make the derived request body incomplete.
  -- .63.1.6.2.3 (slice B): TX-BEARING receipts-consensus enforcement. execution-specs
  -- apply_body recomputes receipt_root = root(receipts_trie) and block_logs_bloom and hard-
  -- rejects on a header mismatch (fork.py 368-371). Encode the materialized per-tx receipt
  -- records (status||cumulative_gas||bloom||logs, with the .2.1 log descriptors @56) into one
  -- RLP list, then validate header.receipts_root == MPT(indexed(receipts)) AND header.bloom ==
  -- OR(receipt blooms) via the shared consensus validator. Helper failures are not
  -- normalized into acceptance; wrong or incomplete upstream values fail visibly here.
  -- Confirmed root/bloom mismatches reject as before.
  "  bnez a0, .Lbv_receipt_logs_helper_status\n" ++
  -- `bv_block_log_overflow` is recorded separately from the helper return status because
  -- block_log_window_snapshot can set it before this tail runs. Do not accept on overflow:
  -- derived EIP-6110 deposits are computed from captured logs, and an uncaptured log could
  -- be a deposit event. Reject through the requests_hash class instead of trusting an
  -- incomplete derived deposit body.
  "  la t2, bv_block_log_overflow; ld t2, 0(t2); bnez t2, .Lbv_requests_hash_fail\n" ++
  -- 8uld3.4: derive EIP-6110 deposit requests from EXECUTION-produced logs and
  -- verify the final requests_hash against the value that the early header-hash
  -- check already committed to (`erh_requests_hash`). This stops trusting the
  -- SSZ execution_requests.deposits body: a block whose SSZ deposits match the
  -- header but whose receipts contain different deposit logs is rejected here.
  -- The scratch sizes mirror the named block-log and request-body arenas; over-capacity
  -- in the captured block-log stream rejects above rather than skipping this check.
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
  "  la t2, c1_dlen; ld t2, 0(t2); bnez t2, .Lbv_deposit_body_ready\n" ++
  "  la t2, bv_deposit_runtime_capture_complete; ld t2, 0(t2); bnez t2, .Lbv_deposit_body_ready\n" ++
  blockVerdictDirectDepositFallback ++
  ".Lbv_deposit_after_direct:\n" ++
  ".Lbv_deposit_body_ready:\n" ++
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
  -- 4 unsupported tx type, 5 record-count capacity overflow. Any nonzero status
  -- means the enforced receipt list was not checked precisely, so fail.
  "  la t2, bv_receipts_encoder_status; sd a0, 0(t2)\n" ++
  "  bnez a0, .Lbv_receipts_helper_fail\n" ++
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
  "  j .Lbv_receipts_helper_fail\n" ++
   ".Lbv_receipts_accept:\n" ++
   -- dispatch_tx_runtime_code produces 0 on complete replay and 1..7 on a
   -- conservative bail; the single-tx destroyed-empty detector may replace a
   -- successful result with 62.  Every nonzero route bypasses the single-tx
   -- all-account storage/tuple comparators, so none may accept based only on a
   -- matching attacker-chosen receipts root.
   -- #11119: this is a DISPATCH-status bail, not a storage-omit comparator.
   -- Formerly jumped to .Lbv_bal_storage_omit_fail (bv_fail=36), which lied
   -- about the cause.  Omit property stays CONTAINER_DEPENDENT under 37.
   "  la t0, bv_dispatch_runtime_status; ld t0, 0(t0); bnez t0, .Lbv_dispatch_runtime_status_fail\n" ++
   "  li a0, 1; j .Lbv_ret\n" ++
  -- #11170: deleted dead `.Lbv_receipts_no_runtime_gas` ACCEPT arm (0 branch
  -- targets). It was the sole bypass of `bv_dispatch_runtime_status` — wiring
  -- it would accept with nonzero dispatch status (latent FA). Live accept above
  -- is the only reader of that cell.
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
  ".Lbv_chain_id_gate_fail:\n" ++        -- evm-asm-7zzfv: chain_id(tx) present and != block chain id (WrongChainIdError)
  "  li t0, 57; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_gas_fail:\n" ++
  "  li t0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_code_preimage_fail:\n" ++
  "  li t0, 11; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_parse_fail:\n" ++
  "  li t0, 12; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_rlp_limit_fail:\n" ++
  "  li t0, 13; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip8037_gas_fail:\n" ++
  -- This tail encodes only the documented eip8037_tx_gas_gate statuses 1..3
  -- as codes 8..10.  Two MTx creation-prefix callers currently arrive with
  -- raw header.gas_limit in a0; retain their reject but make that contract
  -- violation explicit as sentinel 63 rather than aliasing a normal gas code.
  "  li t2, 1; bltu a0, t2, .Lbv_eip8037_gas_invalid_status\n" ++
  "  li t2, 3; bgtu a0, t2, .Lbv_eip8037_gas_invalid_status\n" ++
  "  addi t0, a0, 7; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip8037_gas_invalid_status:\n" ++
  "  li t0, 63; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_eip7702_nonce_reuse_fail:\n" ++
  "  li t0, 14; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_blockhash_headers_fail:\n" ++
  "  li t0, 15; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_syscode_identity_fail:\n" ++
  "  li t0, 65; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
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
  -- Keep this upper-bound failure distinct from the recipient / BAL code-41
  -- family.  The terminal route and verdict are unchanged; this only gives
  -- OUTPUT+112 a stable diagnostic identity for the gas-over arm.
  "  li t0, 62; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_mtx_recipient_unresolvable_fail:\n" ++   -- fhsxz.2.4.2.57.11.6.5.4 (e): mtx tx recipient unresolvable at pre-state root (incomplete witness)
  "  li t0, 47; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_block_hash_mismatch:\n" ++
  "  li t0, 31; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  -- #11118: removed dead sinks storage_mismatch(34), recipient_field(35), reads(38).
  -- NOTE: code 35 remains live on .Lbv_block_state_gas_fail above (unrelated).
  -- NOTE: bal_storage_matches_exec_log unlinked from guest (#10681 dead subtree).
  -- storage_omit(36): sink retained for the named property; currently unreachable
  -- (#11119 / PR #11131 retargeted dispatch bail to code 64). Reverse storage
  -- allaccounts (37) unlinked #10681 (hash survivor). Standalone 36 waits on
  -- container convergence.
  ".Lbv_bal_storage_omit_fail:\n" ++       -- bmvmx.1.6.5 named property; unreachable (#11119)
  "  li t0, 36; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_dispatch_runtime_status_fail:\n" ++  -- #11119: bv_dispatch_runtime_status ≠ 0 at receipts-accept
  "  li t0, 64; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_allaccounts_fail:\n" ++        -- bmvmx.1.6.4.3: a non-recipient BAL account's storage != execution
  "  li t0, 37; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_sender_bal_fail:\n" ++             -- bmvmx.1.6.3: BAL sender post balance != execution-derived (pre - gas_charge - value)
  "  li t0, 39; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  -- This is deliberately a catch-all legacy code, not a mechanism identifier:
  -- transaction-nonce validity; EIP-7702 self-authority/auth parsing/recovery/signer
  -- binding; and MTx setup/materialization/inclusion/state-gas helper failures reach it.
  ".Lbv_sender_nonce_fail:\n" ++
  "  li t0, 40; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  -- Retirement-scoped: declared-versus-execution BAL final-nonce comparison.
  -- Code 59 retires with the storage/nonstorage BAL families in the 10680 inventory;
  -- code 40's transaction-validity/auth reachers deliberately do not.
  ".Lbv_mtx_sender_final_nonce_fail:\n" ++  -- bmvmx.5.5.2: declared BAL sender final nonce != execution-derived final nonce
  "  li t0, 59; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_recipient_bal_fail:\n" ++          -- bmvmx.1.6.3: BAL contract-recipient post balance != recipient_pre + tx.value
  "  li t0, 41; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  -- #11245: removed dead sink .Lbv_bal_tuple_fail (code 42); rejection now via hash 60/61.
  -- #11118: removed dead sinks code_covers(43), code_consistent(46).
  ".Lbv_bal_nonstorage_fail:\n" ++         -- i3djw.3: a non-recipient BAL account's declared balance/nonce change != exec non-storage effect
  "  li t0, 44; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_map_fail:\n" ++               -- #11104: account-write builder attribution mismatch
  "  li t0, 66; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_bal_nonstorage_covers_fail:\n" ++  -- i3djw.3 reverse: exec net-changed an account's balance/nonce that the BAL omits
  "  li t0, 45; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_sender_upfront_fail:\n" ++         -- bmvmx.2: sender_pre_balance < gas_limit*max_fee + value (InsufficientBalanceError)
  "  li t0, 48; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_fee_invalid_fail:\n" ++           -- bmvmx.4: tx fee invalid (max_fee < base_fee, or priority > max_fee) -> check_transaction reject
  "  li t0, 49; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_mtx_sender_balance_fail:\n" ++    -- bmvmx.5.5.2.2.3 (B2.3): a multi-tx pure-payer sender's BAL final balance != pre - Σ(actual gas+value debit)
  "  li t0, 57; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_fixed_arena_overflow_fail:\n" ++
  "  li t0, 58; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero\n" ++
  ".Lbv_zero:\n" ++
  "  li a0, 0\n" ++
  ".Lbv_ret:\n" ++
  -- Rebuilt-BAL digest comparison (survivor for #10612/#11245). Runs after
  -- granular paths; status is bound ACCEPT-only below (fail 60/61). Preserve
  -- the original a0 verdict across the serializer (mutates builder order).
  "  sd a0, 40(sp)\n" ++
  -- Inputs that never passed the BAL decoding/gas gate have no valid slice to
  -- inspect.  Use the same structural reachability condition as the granular
  -- comparators, not a hand-rolled nonzero-pointer test.
  "  li t0, 3; la t1, bv_bal_shadow_status; sd t0, 0(t1); la t1, bv_bal_shadow_ready; ld t1, 0(t1); beqz t1, .Lbv_shadow_done\n" ++
  -- The block body has already materialized NPR = SSZ_BASE + 16.  Use that
  -- stable cell rather than an ambient register at this late terminal seam.
  "  la t0, bv_bal_shadow_emit_storage_changes; sd zero, 0(t0); la t0, bv_bal_shadow_emit_storage_reads; sd zero, 0(t0); la t0, bv_bal_shadow_emit_balance_changes; sd zero, 0(t0); la t0, bv_bal_shadow_emit_nonce_changes; sd zero, 0(t0); la t0, bv_bal_shadow_emit_code_changes; sd zero, 0(t0)\n" ++
  "  la t0, bv_npr_p; ld a0, 0(t0); addi a0, a0, -16; la a1, bv_bal_shadow_scratch; jal ra, bal_serializer_verify\n" ++
  "  la t0, bv_bal_shadow_status; sd a0, 0(t0)\n" ++
  -- `verify`'s rebuild has measured the outer payload.  Add the outer RLP
  -- header to obtain the whole rebuilt BAL byte length, and retain the input
  -- slice length beside it; neither value is a verdict input.
  "  la t0, bal_serializer_outer_payload; ld a0, 0(t0); jal ra, bal_rlp_list_header_len; la t0, bal_serializer_outer_payload; ld t1, 0(t0); add a0, a0, t1; la t0, bv_bal_shadow_rebuilt_len; sd a0, 0(t0)\n" ++
  "  la t0, bv_bal_len; ld t1, 0(t0); la t0, bv_bal_shadow_supplied_len; sd t1, 0(t0)\n" ++
  -- #11120 gas-on-built: after rebuild_hash the builder is incorporated+sorted.
  -- Count bal_items from builder (shape C); reject ACCEPT paths that exceed.
  -- Skip when rebuild failed (status 2) — no well-formed built list.
  "  la t0, bv_bal_shadow_status; ld t0, 0(t0)\n" ++
  "  li t1, 2; beq t0, t1, .Lbv_shadow_done\n" ++
  "  la t0, bv_block_gas_limit; ld a0, 0(t0)\n" ++
  "  jal ra, bal_gas_valid_from_builder\n" ++
  "  beqz a0, .Lbv_shadow_done\n" ++
  "  ld t0, 40(sp); li t1, 1; bne t0, t1, .Lbv_shadow_done\n" ++
  "  li t0, 7; la t1, bv_fail_code; sd t0, 0(t1); sd zero, 40(sp)\n" ++
  ".Lbv_shadow_done:\n" ++
  "  ld a0, 40(sp)\n" ++
  -- GH #10680: bind the rebuilt-BAL digest into the verdict.  The comparison
  -- itself is unchanged -- `bal_serializer_verify` above already rebuilds from the
  -- producer arenas, hashes the supplied BAL, and returns 0 match / 1 differ /
  -- 2 rebuild-failed.  This only makes that existing return participate.
  --
  -- THE BINDING CONTRACT, which is what makes the FR delta attributable:
  --   * bind ONLY when the original verdict is ACCEPT (`a0 == 1`) and
  --     `bv_bal_shadow_ready == 1`.  Every existing `a0 == 0` reject flows through
  --     untouched, so NO existing fail code changes meaning and every current test
  --     expectation survives.
  --   * therefore the change can only ever convert an ACCEPT into a REJECT.  IT
  --     CANNOT CREATE A FALSE ACCEPT -- there is no path by which it raises FA.
  --   * `a0` is compared against 1 rather than tested nonzero: an accept route that
  --     ever returned some other nonzero value would be UNDER-bound (fewer new
  --     rejects), which is the safe direction and shows up as an FR delta below the
  --     predicted 832 rather than as a silent behaviour change.
  --
  -- TWO codes, not one.  60 is a genuine BAL mismatch; 61 is a rebuild failure,
  -- which covers canonical-sort failure and arena overflow.  Status 2 measures ZERO
  -- across the whole BAL corpus today so 61 should never fire -- but collapsing them
  -- would make a capacity limit indistinguishable from a wrong BAL the first time it
  -- does.  Neither reuses the gaps at 8, 9 or 18: a gap may be a retired code, and
  -- this codebase has already been bitten by one code serving two conditions.
  --
  -- Deliberately does NOT retire any granular BAL check.  Those carry skip lists
  -- that are accommodations for producer gaps, so retiring them is a SECOND and
  -- separately unpredictable FR event -- one variable at a time.
  "  li t0, 1; bne a0, t0, .Lbv_bal_digest_bound\n" ++
  "  la t0, bv_bal_shadow_ready; ld t0, 0(t0); beqz t0, .Lbv_bal_digest_bound\n" ++
  "  la t0, bv_bal_shadow_status; ld t0, 0(t0)\n" ++
  "  li t1, 1; beq t0, t1, .Lbv_bal_digest_mismatch\n" ++
  "  li t1, 2; beq t0, t1, .Lbv_bal_digest_rebuild_fail\n" ++
  "  j .Lbv_bal_digest_bound\n" ++
  ".Lbv_bal_digest_mismatch:\n" ++
  "  li t0, 60; la t1, bv_fail_code; sd t0, 0(t1); li a0, 0; j .Lbv_bal_digest_bound\n" ++
  ".Lbv_bal_digest_rebuild_fail:\n" ++
  "  li t0, 61; la t1, bv_fail_code; sd t0, 0(t1); li a0, 0\n" ++
  ".Lbv_bal_digest_bound:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

-- GH #10680 binding contract, pinned so a later edit cannot loosen it silently.
-- The ACCEPT-only guard is the whole reason the FR delta is attributable and the
-- reason no false accept is possible; the two distinct codes are the reason a
-- capacity limit stays distinguishable from a wrong BAL.
#guard (blockVerdictReceiptsTail.splitOn "li t0, 1; bne a0, t0, .Lbv_bal_digest_bound").length == 2
#guard (blockVerdictReceiptsTail.splitOn "la t0, bv_bal_shadow_ready; ld t0, 0(t0); beqz t0, .Lbv_bal_digest_bound").length == 2
#guard (blockVerdictReceiptsTail.splitOn "li t0, 60; la t1, bv_fail_code").length == 2
#guard (blockVerdictReceiptsTail.splitOn "li t0, 61; la t1, bv_fail_code").length == 2
-- GH #10848: this tail is a status encoder, not a raw-value sink.  The two
-- guards pin both sides of its documented 1..3 domain; the sentinel makes an
-- out-of-contract caller observable without changing its reject verdict.
#guard (blockVerdictReceiptsTail.splitOn "li t2, 1; bltu a0, t2, .Lbv_eip8037_gas_invalid_status").length == 2
#guard (blockVerdictReceiptsTail.splitOn "li t2, 3; bgtu a0, t2, .Lbv_eip8037_gas_invalid_status").length == 2
#guard (blockVerdictReceiptsTail.splitOn "li t0, 63; la t1, bv_fail_code; sd t0, 0(t1); j .Lbv_zero").length == 2
-- Each code must also DROP THE VERDICT in the same breath as recording itself: a
-- fail code stored without `li a0, 0` would report a mismatch while still accepting
-- the block, which is the one failure mode of this change that no test would catch.
-- (Non-collision with the codes already in use is NOT checkable here -- those are
-- stored from other modules -- so it is established in the PR body, not by a guard.)
#guard (blockVerdictReceiptsTail.splitOn "li t0, 60; la t1, bv_fail_code; sd t0, 0(t1); li a0, 0").length == 2
#guard (blockVerdictReceiptsTail.splitOn "li t0, 61; la t1, bv_fail_code; sd t0, 0(t1); li a0, 0").length == 2

end EvmAsm.Codegen
