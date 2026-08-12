/-
  EvmAsm.Codegen.Programs.BlockVerdictFunction

  Main block_verdict assembly string, split from BlockVerdict.lean for FileSizeGuard.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictTransactions
import EvmAsm.Codegen.Programs.BlockVerdictReceiptsTail
import EvmAsm.Codegen.Programs.BlockVerdictMtxTail
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate
import EvmAsm.Codegen.Programs.BlockVerdictCreationStage
import EvmAsm.Codegen.Programs.BlockVerdictExactGas
import EvmAsm.Codegen.Programs.BlockVerdictGasGatePrelude
import EvmAsm.Codegen.Programs.BlockVerdictMtxCoinbase
import EvmAsm.Codegen.Programs.BlockVerdictMtxRuntime
import EvmAsm.Codegen.Programs.BlockVerdictEip7702SenderAuth
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPrecompileGas
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferPublish
import EvmAsm.Codegen.Programs.BlockVerdictBmvMx
import EvmAsm.Codegen.Programs.BlockVerdictWithdrawalEffects
import EvmAsm.Codegen.Programs.BlockVerdictFunctionTail
namespace EvmAsm.Codegen

/-! ## block_verdict -- step2_verdict with the FULL (system + withdrawal) recompute.
    a0 = params ptr (the step2_verdict struct)   a1 = SSZ_BASE
    a0 (output) = verdict bit. -/
def blockVerdictFunction : String :=
  simpleTransferIntrinsicGasFunction ++ "\n" ++
  "block_verdict:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                   # params\n" ++
  "  mv s3, a1                   # SSZ_BASE\n" ++
  -- fhsxz.2.4.2.57.11.6.5: stash the parent (PRE-state) header RLP ptr/len so
  -- dispatch_tx_runtime_code's witness lookups use the PRE-state root (witness root),
  -- not sv_this_rlp (this block's POST-state header). 8(s0)/16(s0) is the parent header.
  "  ld t0, 8(s0); la t1, sv_pre_rlp_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 16(s0); la t1, sv_pre_rlp_len; sd t0, 0(t1)\n" ++
  -- 5tmlt.3: globalize the witness.state ptr/len (params+80/+88) so the EIP-7702
  -- existing-authority refund can resolve an authority's PRE-state code (prior-block
  -- delegation) via code_at_header_state_root, mirroring the spec's get_code check.
  "  ld t0, 80(s0); la t1, bv_witness_state_ptr; sd t0, 0(t1)\n" ++
  "  ld t0, 88(s0); la t1, bv_witness_state_len; sd t0, 0(t1)\n" ++
  "  la t0, bv_fail_code; sd zero, 0(t0)\n" ++
  "  la t0, create_deposit_witness_incomplete_flag; sd zero, 0(t0)\n" ++
  "  la t0, create_deposit_malformed_flag; sd zero, 0(t0)\n" ++
  "  la t0, ib_deleg_cahsr_unresolved_flag; sd zero, 0(t0)\n" ++
  "  la t0, bv_header_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_state_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_tx_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_gas_left_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_refund_counter_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_calldata_floor_ptr; sd zero, 0(t0)\n" ++
  "  la t0, bv_eip4788_current_fast_seen; sd zero, 0(t0)\n" ++
  "  la t0, bv_pending_upfront_balance_flag; sd zero, 0(t0)\n" ++
  "  la t0, bv_pending_recipient_credit_flag; sd zero, 0(t0)\n" ++
  "  la t0, bvgr_runtime_count; sd zero, 0(t0)\n" ++
  "  ld a0, 0(s0); ld a1, 32(s0); ld a2, 40(s0); ld a3, 48(s0); ld a4, 56(s0); ld a7, 96(s0)\n" ++
  "  la a5, sv_this_rlp; la a6, sv_this_rlp_len\n" ++
  "  jal ra, block_header_ssz_to_rlp\n" ++
  "  la t0, bv_block_hash_check_enabled; ld t0, 0(t0); beqz t0, .Lbv_block_hash_ok\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); la a2, bv_block_hash\n" ++
  "  jal ra, block_hash_from_header\n" ++
  -- Spec-alignment: execution-specs compares the block-hash digest. Do not
  -- strengthen this to raw-header comparison; see docs/agents/spec-alignment-doctrine.md §7.
  "  la t0, bv_block_hash; ld t1, 0(s0); addi t1, t1, 472; li t2, 32\n" ++
  ".Lbv_block_hash_cmp:\n" ++
  "  beqz t2, .Lbv_block_hash_ok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_block_hash_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_block_hash_cmp\n" ++
  ".Lbv_block_hash_ok:\n" ++
  "  ld a0, 0(s0); la t0, sv_this_rlp_len; ld a1, 0(t0); mv a2, s3\n" ++
  "  jal ra, block_rlp_rebuilt_size\n" ++
  "  bnez a0, .Lbv_block_rlp_parse_fail\n" ++
  "  la t0, bv_block_rlp_len; sd a1, 0(t0)\n" ++
  "  li t1, 0x800000; bgtu a1, t1, .Lbv_block_rlp_limit_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 8(s0); ld a3, 16(s0)\n" ++
  "  jal ra, validate_header_rlp_pair\n" ++
  "  mv s1, a0\n" ++
  "  la t0, bv_header_status; sd s1, 0(t0)\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0); ld a2, 64(s0); ld a3, 72(s0)\n" ++
  "  jal ra, block_validate_withdrawals_root_indexed\n" ++
  "  la t0, bv_withdrawals_root_status; sd a0, 0(t0)\n" ++
  "  la t0, bv_withdrawals_root_valid; sd a1, 0(t0)\n" ++
  "  bnez a0, .Lbv_withdrawals_root_fail\n" ++
  "  beqz a1, .Lbv_withdrawals_root_fail\n" ++
  blockVerdictBmvMxPrecomputePrefix ++
  -- The compact `sv_params` record stores the SSZ payload pointer at +0;
  -- the payload's state-root field is at +52.  Keep the expected-root pointer
  -- in the payload, not at +52 inside the params record itself.
  "  la t0, bsr_header_state_root_p; ld t1, 0(s0); addi t1, t1, 52; sd t1, 0(t0)\n" ++
  "  ld a0, 24(s0); ld a1, 80(s0); ld a2, 88(s0); ld a3, 64(s0); ld a4, 72(s0)\n" ++
  "  la a5, sv_recomputed; mv a6, s3\n" ++
  "  jal ra, block_state_root_pre_accounts\n" ++
  "  bnez a0, .Lbv_state_fail\n" ++
  "  bnez s1, .Lbv_header_fail\n" ++
  "  # NO-TRANSACTION gate: this verdict does NOT validate transactions, so it can\n" ++
  "  # only soundly judge no-tx blocks. A tx-bearing INVALID block whose invalid tx\n" ++
  "  # is rejected (no state change) would otherwise match the recompute -> false\n" ++
  "  # positive. tx list is empty iff transactions_offset == withdrawals_offset.\n" ++
  -- `blockVerdictBmvMxPrecomputePrefix` has already initialized `bv_exec_p`
  -- to `s3 + 60`, the execution-payload SSZ base.  `0(s0)` is not populated
  -- until the later extracted-params stage; overwriting the global here made
  -- the no-transaction gas gate read an unrelated zero word.
  "  la t5, bv_exec_p; ld t4, 0(t5)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  la t5, bv_tx_off; sd a0, 0(t5)\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 508; jal ra, bgv_u32le   # withdrawals_offset\n" ++
  "  la t5, bv_tx_off; ld t3, 0(t5)\n" ++
  "  bgtu a0, t3, .Lbv_tx_present # wd_off > tx_off => transactions present\n" ++
  -- wsvlq: NO-TRANSACTION (withdrawal/system-only) block. execution-specs apply_body
  -- increments block_gas_used / block_state_gas_used ONLY per transaction; system txs
  -- and withdrawals do not touch them (fork.py:1199-1202, 734-798, 1230-1249). So a
  -- no-tx block has block_gas_used = 0 and header.gas_used == max(.,.) must be 0; a
  -- nonzero header.gas_used raises InvalidBlock. Verify it here instead of trusting it.
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # header.gas_used\n" ++
  "  bnez a0, .Lbv_notx_gas_used_fail\n" ++
  -- .63.1.6.2.3 (slice A): NO-TX receipts consensus. execution-specs apply_body
  -- recomputes receipt_root = root(receipts_trie) and block_logs_bloom =
  -- logs_bloom(block_logs) and hard-rejects on a header mismatch (fork.py
  -- 368-371). A no-tx block has an EMPTY receipts trie and ZERO block logs
  -- (system txs and withdrawals contribute neither receipts nor block_logs),
  -- so header.receipts_root must be the empty-trie root and header.bloom must
  -- be 256 zero bytes. The guest never checked either — the audited
  -- false-accept (hermes-c3, bead .63.1.6): a crafted no-tx block with a
  -- tampered bloom/receipt_root and a self-consistent payload.block_hash
  -- passed every gate. Compute the empty indexed-trie root through the real
  -- validator (count = 0) and compare the extracted header bloom to zeros.
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bvrri_value_descs; li a3, 0\n" ++
  "  jal ra, block_validate_receipts_root_indexed\n" ++
  "  bnez a0, .Lbv_notx_receipts_root_fail\n" ++
  "  beqz a1, .Lbv_notx_receipts_root_fail\n" ++
  "  la a0, sv_this_rlp; la t0, sv_this_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_header_bloom\n" ++
  "  jal ra, header_extract_logs_bloom\n" ++
  "  bnez a0, .Lbv_notx_bloom_fail\n" ++
  "  la a0, bv_header_bloom; la a1, bv_zero_bloom; la a2, bv_bloom_eq_out\n" ++
  "  jal ra, bloom_eq\n" ++
  "  la t0, bv_bloom_eq_out; ld t0, 0(t0); beqz t0, .Lbv_notx_bloom_fail\n" ++
  "  j .Lbv_after_tx_gate\n" ++
  blockVerdictEmptyTransactionCheckAsm ++
  -- #11833 / #11797 M1: retired guest-invented bv_fail 4 (`.Lbv_no_bal_for_tx`).
  -- Spec has no pre-body supplied-BAL presence test; sender gas path never used
  -- `bsr_bal_*`. Empty/malformed BAL dies later (hash / other post-body).
  "  # Any included transaction must consume nonzero gas. This catches rejected\n" ++
  "  # tx payloads whose state/BAL roots otherwise match the conservative replay.\n" ++
  "  la t5, bv_exec_p; ld t4, 0(t5); addi a0, t4, 420; jal ra, bgv_u64le   # gas_used\n" ++
  "  beqz a0, .Lbv_zero_gas_used\n" ++
  ".Lbv_after_tx_gate:\n" ++
  "  # execution-specs is_valid_versioned_hashes: SSZ NPR.versioned_hashes must\n" ++
  "  # equal the concatenation of all EIP-4844 tx blob_versioned_hashes.\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_npr_p; sd t0, 0(t2)\n" ++
  "  addi a0, t0, 4; jal ra, bgv_u32le         # versioned_hashes offset\n" ++
  "  mv t3, a0\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 40; jal ra, bgv_u32le # execution_requests offset\n" ++
  "  bltu a0, t3, .Lbv_versioned_hashes_fail\n" ++
  "  sub a2, a0, t3              # SSZ versioned_hashes byte length\n" ++
  "  la t2, bv_versioned_hashes_len; sd a2, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, t3\n" ++
  "  la t2, bv_exec_p; ld a0, 0(t2)\n" ++
   "  jal ra, ssz_tx_list_versioned_hashes_match\n" ++
   "  bnez a0, .Lbv_versioned_hashes_fail\n" ++
   -- #11839: header.blob_gas_used comparison moved post-body (ReceiptsTail after
   -- exact gas / roots) to match fork.py:386-387. KEEP the price producer here:
   -- amsterdam_blob_gas_price_u256 writes bsg_blob_price_be consumed by the body
   -- (MtxRuntime upfront blob fee, MtxTail B2.2 debit). Moving the producer with
   -- the comparison would leave type-3 body fee accounting on a stale price.
   "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 520; jal ra, bgv_u64le\n" ++
   "  la a1, bsg_blob_price_be; jal ra, amsterdam_blob_gas_price_u256\n" ++
   "  bnez a0, .Lbv_blob_gas_used_fail\n" ++
   "  mv a0, s3\n" ++
  "  la t2, bv_exec_p; ld a1, 0(t2)\n" ++
  "  jal ra, public_keys_valid\n" ++
  "  bnez a0, .Lbv_public_keys_fail\n" ++
  -- bmvmx.3.2: bind each witness public_keys[i] to the i-th transaction's
  -- recovered signer key (execution-specs recover_sender_from_public_key over
  -- every tx). public_keys_valid only checked count + 65-byte SEC1 shape; this
  -- recovers the sender from each signature and rejects on any mismatch /
  -- recovery failure, closing the sender-attribution false-accept (a lying
  -- witness can otherwise attribute a tx to an attacker-chosen account). Needs
  -- bv_tx_list_ptr/len (set above), bv_public_keys_ptr (set by public_keys_valid),
  -- and bv_chain_id (captured by chain_config_valid).
  "  jal ra, verify_public_keys_match_senders\n" ++
  "  bnez a0, .Lbv_public_keys_sender_fail\n" ++
  -- evm-asm-7zzfv (v0.6.0 item 8): per-tx chain-id-vs-block gate,
  -- fork.py:1051-1055 process_transaction: reject the block when chain_id(tx)
  -- is present and != block_env.chain_id (WrongChainIdError). Typed txs embed
  -- their own chain id in the signing hash, so the sender recovery above
  -- succeeds regardless of the block chain id -- without this gate a
  -- wrong-chain typed tx was a verdict false-accept.
  "  jal ra, block_verdict_chain_id_gate\n" ++
  "  bnez a0, .Lbv_chain_id_gate_fail\n" ++
   "  # Decode declared BAL slice + capture gas_limit for late gas-on-built (#11120).\n" ++
  "  # Spec validate_block_access_list_gas_limit runs on the BUILT list after\n" ++
  "  # build_block_access_list (fork.py:932-936); early gas-on-declared removed.\n" ++
  "  mv a0, s3; jal ra, bgv_u32le\n" ++
  "  add t0, s3, a0              # NPR = SSZ_BASE + outer.offsets[0]\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2)\n" ++
  "  la t2, bv_npr_p;  sd t0, 0(t2)\n" ++
  "  addi a0, t1, 528; jal ra, bgv_u32le        # bal_off\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); add a0, t1, a0   # bal_start\n" ++
  "  la t2, bv_bal_start; sd a0, 0(t2)\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); addi a0, t0, 4; jal ra, bgv_u32le   # vh_off\n" ++
  "  la t2, bv_npr_p; ld t0, 0(t2); add a1, t0, a0   # bal_end\n" ++
  "  la t2, bv_bal_start; ld t3, 0(t2); sub a1, a1, t3   # bal_len\n" ++
  "  la t2, bv_bal_len; sd a1, 0(t2)\n" ++
  "  la t2, bv_exec_p; ld t1, 0(t2); addi a0, t1, 412; jal ra, bgv_u64le   # gas_limit\n" ++
  "  la t2, bv_block_gas_limit; sd a0, 0(t2)\n" ++
  -- Decoded BAL slice ready for granular comparators + Path A observer.
  -- Gas-on-built runs at Lbv_ret after rebuild (bal_gas_valid_from_builder).
  "  li t0, 1; la t2, bv_bal_shadow_ready; sd t0, 0(t2)\n" ++
  "  # Witness integrity: for every BAL account with non-empty pre-state code,\n" ++
  "  # witness.codes must contain that code hash, matching execution-specs'\n" ++
  "  # WitnessState.get_code behavior for missing non-empty code preimages.\n" ++
  "  # Pure BAL account-touch rows are safe to ignore only for withdrawal-only\n" ++
  "  # blocks: zero-amount withdrawals may touch an account without reading code.\n" ++
  "  la t2, bbcv_skip_touch_only; sd zero, 0(t2)\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 504; jal ra, bgv_u32le        # transactions_offset\n" ++
  "  mv t3, a0\n" ++
  "  ld t4, 0(s0)\n" ++
  "  addi a0, t4, 508; jal ra, bgv_u32le        # withdrawals_offset\n" ++
  "  bleu a0, t3, .Lbv_code_preimage_no_txs\n" ++
  "  sub t5, a0, t3                             # tx list byte length\n" ++
  "  li t6, 4; bltu t5, t6, .Lbv_code_preimage_no_txs\n" ++
  "  ld t4, 0(s0); add t4, t4, t3               # tx list ptr\n" ++
  "  mv a0, t4; jal ra, bgv_u32le               # first offset = 4 * tx_count\n" ++
  "  andi t6, a0, 3; bnez t6, .Lbv_code_preimage_no_txs\n" ++
  "  srli t6, a0, 2\n" ++
  "  beqz t6, .Lbv_code_preimage_no_txs\n" ++
  "  bgtu a0, t5, .Lbv_code_preimage_no_txs\n" ++
  "  j .Lbv_code_preimage_flag_done             # transactions present\n" ++
  ".Lbv_code_preimage_no_txs:\n" ++
  "  ld t5, 72(s0)\n" ++
  "  beqz t5, .Lbv_code_preimage_flag_done\n" ++
  "  li t6, 1; la t2, bbcv_skip_touch_only; sd t6, 0(t2)\n" ++
  ".Lbv_code_preimage_flag_done:\n" ++
  "  li t6, 1; la t2, bbcv_fee_recipient_valid; sd t6, 0(t2)\n  la a0, bbcv_fee_recipient; ld a1, 0(s0); addi a1, a1, 32; li a2, 20\n  jal ra, mset_memcpy\n" ++
  "  # GH #11410: the static BAL row-shape preimage scan is retired. Preimage\n" ++
  "  # coverage is enforced dynamically from the execution code-read set\n" ++
  "  # (code_read_fetch) in the receipts tail (fail 11, .Lbv_code_preimage_fail).\n" ++
  "  # Upfront sender gas pre-charge gate for the currently parse-supported\n" ++
  "  # one-transaction path. Use the selected public key tail (x||y) and the\n" ++
  "  # pre-account record table materialized by block_state_root.\n" ++
  blockVerdictMtxRuntimeLoop ++
  -- #11163: shared-body arm jumps here after move_ether.  Lane-2 success/fail
  -- exits rejoin dtrc settle via .Ldtrc_mtx_precompile_{success,failure}.
  blockVerdictSimpleTransferPrecompileGasAsmFor "bv_mtx_ctx" ++
  blockVerdictSimpleTransferPublishAsmFor "bv_mtx_ctx" ++
  blockVerdictFunctionTail ++ "\n"

end EvmAsm.Codegen
