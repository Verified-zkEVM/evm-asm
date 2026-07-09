/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxTail

  Multi-tx exec-vs-BAL validation tail of block_verdict (the .Lbv_mtx_done block:
  the A1 skip-list builder, the B1 sender-final-nonce check, and the A2a all-accounts
  non-storage comparators), split out of BlockVerdictFunction.lean to stay under the
  1500-line file cap (bmvmx.5.5 child). Pure asm-string fragment, concatenated back
  byte-identically via blockVerdictMtxValidationTail. The .Lbv_* labels are all local
  to the single assembled block_verdict function, so splitting the string does not
  affect label resolution.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.NonstorageEffectLog

namespace EvmAsm.Codegen

/-- Multi-tx exec-vs-BAL validation tail of `block_verdict` (skip-list build + B1
    sender-nonce + A2a non-storage comparators), concatenated at .Lbv_mtx_done. -/
def blockVerdictMtxValidationTail : String :=
  -- bmvmx.5.5.1 (umbrella-A1): build the MULTI-TX skip-list that the all-accounts
  -- exec-vs-BAL comparators (@1032-1110, run only on the single-tx path today) must
  -- skip. The single-tx i3djw_skip_list is the fixed 8 entries {recipient, sender,
  -- coinbase, six system addresses}; a multi-tx block has up to 2N+1 such
  -- gas/value-coupled accounts plus the same six system addresses. We are
  -- at .Lbv_mtx_done, so EVERY tx reached a status-0 supported shape -> re-deriving
  -- each is safe (address_from_pubkey already ran @474, multi_tx_nth_context @438):
  --   skip[2i]   = sender_i    = address_from_pubkey(public_keys[i]+1)   (as @473-474)
  --   skip[2i+1] = recipient_i = multi_tx_nth_context(bv_mtx_skip_ctx,i)+72 (pure re-extract)
  --   skip[2N]   = coinbase     = fee_recipient (bv_exec_p+32)            (as @161-164)
  --   skip[2N+1..2N+6] = the genesis system/predeploy contracts plus SYSTEM_ADDRESS
  -- count = 2N+7. 32-byte-strided, address in the first 20 bytes. BEHAVIOR-NEUTRAL:
  -- nothing reads bv_mtx_skip_list yet (umbrella-A2 wires it into the comparators);
  -- built here so the existing multi-tx fixtures exercise the derivation. The build
  -- loop's cursor lives in bv_mtx_skip_idx (memory) so it survives the jal calls;
  -- s0/s3 (params/SSZ_BASE) are callee-saved and preserved across them.
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_skl_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_skl_done\n" ++
  "  slli t3, t1, 6; add t4, t3, t1\n" ++                               -- t4 = i*65
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t4; addi a0, t0, 1\n" ++  -- a0 = public_keys[i]+1 (skip 0x04)
  "  slli t5, t1, 6; la a1, bv_mtx_skip_list; add a1, a1, t5\n" ++      -- a1 = &skip[2i] (offset i*64)
  "  jal ra, address_from_pubkey\n" ++
  "  la a0, bv_mtx_skip_ctx; la t0, bv_mtx_skip_idx; ld a1, 0(t0); jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t5, t1, 6; addi t5, t5, 32\n" ++
  "  la t6, bv_mtx_skip_list; add t6, t6, t5\n" ++                      -- t6 = &skip[2i+1] (offset i*64+32)
  "  la t2, bv_mtx_skip_ctx; addi t2, t2, 72; li t3, 0\n" ++            -- src = recipient (ctx+72)
  ".Lbv_skl_rcopy:\n  li t4, 20; beq t3, t4, .Lbv_skl_rcopy_d\n  add t4, t2, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4); addi t3, t3, 1; j .Lbv_skl_rcopy\n.Lbv_skl_rcopy_d:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_skl_loop\n" ++
  ".Lbv_skl_done:\n" ++
  "  la t2, bv_tx_count; ld t2, 0(t2); slli t5, t2, 6; la t6, bv_mtx_skip_list; add t6, t6, t5\n" ++  -- t6 = &skip[2N] (offset N*64)
  "  la t1, bv_exec_p; ld t1, 0(t1); addi t1, t1, 32; li t3, 0\n" ++    -- src = fee_recipient (exec_p+32)
  ".Lbv_skl_cb:\n  li t4, 20; beq t3, t4, .Lbv_skl_cb_d\n  add t4, t1, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4); addi t3, t3, 1; j .Lbv_skl_cb\n.Lbv_skl_cb_d:\n" ++
  "  addi t6, t6, 32\n" ++                                             -- t6 = &skip[2N+1]
  "  la t1, bbcv_sys_2935; li t4, 6\n" ++
  ".Lbv_skl_sys_o:\n  li t3, 0\n" ++
  ".Lbv_skl_sys_i:\n  li t2, 20; beq t3, t2, .Lbv_skl_sys_next\n  add t2, t1, t3; lbu a0, 0(t2); add t2, t6, t3; sb a0, 0(t2); addi t3, t3, 1; j .Lbv_skl_sys_i\n.Lbv_skl_sys_next:\n" ++
  "  addi t1, t1, 20; addi t6, t6, 32; addi t4, t4, -1; bnez t4, .Lbv_skl_sys_o\n" ++
  "  la t2, bv_tx_count; ld t2, 0(t2); slli t3, t2, 1; addi t3, t3, 7; la t0, bv_mtx_skip_count; sd t3, 0(t0)\n" ++  -- count = 2N+7
  -- bmvmx.5.5.2 (umbrella-B1): validate each multi-tx SENDER's BAL FINAL nonce == pre_nonce +
  -- (total count of that sender's txs) -- the multi-tx generalization of the single-tx post-
  -- nonce check (.Lbv_sender_nonce_fail, status 40). An EOA sender's nonce increments once per
  -- tx (no internal code), so final == pre+count for every valid block -> never false-rejects;
  -- catches a BAL forging the sender's final nonce. Post-loop pass; sender_i = skip[2i] (A1),
  -- compacted by b1_sender_count_table into distinct sender/count rows. Conservative skips:
  -- sender absent from BAL, account_at failure, no declared nonce change. Cursor in
  -- bv_mtx_skip_idx walks the distinct table and survives jals via memory.
  "  la a0, bv_mtx_skip_list; la t0, bv_tx_count; ld a1, 0(t0); la a2, bv_b1_sender_table; li a3, " ++ toString bvMtxSenderCountEntries ++ "; la a4, bv_b1_sender_count\n" ++
  "  jal ra, b1_sender_count_table\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++                              -- reject if table build failed (capacity/malformed)
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++                       -- i = 0 over distinct sender table
  ".Lbv_b1_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_b1_sender_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_b1_done\n" ++
  "  li t3, 40; mul t3, t1, t3; la t4, bv_b1_sender_table; add t4, t4, t3\n" ++ -- t4 = &distinct sender entry
  "  ld t6, 32(t4); la t0, bv_b1_count; sd t6, 0(t0)\n" ++             -- stash total count (jal clobbers t6)
  "  ld a0, 8(s0); ld a1, 16(s0); mv a2, t4; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_mtx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_b1_next\n" ++                                       -- sender lookup fail/absent -> skip (conservative)
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0)\n" ++                     -- t0 = pre_nonce (nonce@0)
  "  la t1, bv_b1_count; ld t1, 0(t1); add t0, t0, t1\n" ++            -- expected = pre_nonce + count
  "  la t1, bv_b1_expected; sd t0, 0(t1)\n" ++                         -- stash (jal clobbers)
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); li t3, 40; mul t3, t1, t3; la t4, bv_b1_sender_table; add t4, t4, t3\n" ++ -- reload t4 = &distinct sender entry
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); mv a2, t4; la a3, bv_b1_acct_ptr; la a4, bv_b1_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lbv_b1_next\n" ++                                       -- sender absent from BAL -> skip (conservative)
  "  la t0, bv_b1_acct_ptr; ld a0, 0(t0); la t0, bv_b1_acct_len; ld a1, 0(t0); la a2, bv_b1_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lbv_b1_next\n" ++                                       -- parse fail -> skip
  "  la t0, bv_b1_finals; ld t1, 40(t0); beqz t1, .Lbv_b1_next\n" ++   -- has_nonce == 0 -> skip (conservative)
  "  ld t1, 48(t0)\n" ++                                               -- t1 = BAL declared final nonce
  "  la t0, bv_b1_expected; ld t0, 0(t0)\n" ++                         -- t0 = pre_nonce + count
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                          -- BAL sender final nonce != pre + count -> reject
  ".Lbv_b1_next:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_b1_loop\n" ++
  ".Lbv_b1_done:\n" ++
  -- bmvmx.5.5.2.2.12: B2.2/B2.3 are RELOCATED to run AFTER the gas-result gate
  -- (BlockVerdictReceiptsTail), where bvgr_receipt_gas_increments[i] holds the spec-exact
  -- (regular+state, refund+EIP-7623-floor) per-tx gas_used. The B2.2 sender debit needs that
  -- exact gas, which is 0 here (the gas chain runs later). So skip the B2 block at this early
  -- point and reach it via .Lbv_b2_entry from ReceiptsTail (returns to .Lbv_mtx_b2_return).
  "  j .Lbv_mtx_storage\n" ++
  -- bmvmx.5.5.2.2.2 (umbrella-B2.2): maintain a per-sender running
  -- balance table in tx order. This rejects only if actual post-exec debit
  -- underflows the sender running balance; final BAL-post comparison is B2.3.
  ".Lbv_b2_entry:\n" ++
  "  la t0, bv_b2_count; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_b2_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_b2_done\n" ++
  "  slli t3, t1, 6; la t4, bv_mtx_skip_list; add t4, t4, t3\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); mv a2, t4; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_mtx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  "  la a0, bv_mtx_skip_ctx; la t0, bv_mtx_skip_idx; ld a1, 0(t0); jal ra, multi_tx_nth_context\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  "  la t2, bv_mtx_skip_ctx; ld a0, 8(t2); ld a1, 16(t2); la a2, bv_mtx_base_fee_be; la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  -- bmvmx.5.5.2.2.12: sender GAS debit = bvgr_receipt_gas_increments[i] * eff_price (+ value below).
  -- bvgr_receipt_gas_increments[i] is the SPEC-EXACT per-tx gas_used (regular + EIP-8037 state,
  -- net of EIP-3529 refund and floored by EIP-7623) produced by the gas chain,
  -- which is why this block runs AFTER the gas-result gate (reached via .Lbv_b2_entry from
  -- ReceiptsTail). This replaces the old raw-runtime-gas debit helper plus flat
  -- auth-list settlement, which UNDER-debited type-4 multi-tx senders by the omitted state
  -- gas (bv_fail=57 false-reject on witness_codes_delegation_set_in_same_block / reusing_nonce).
  -- The type-3 BLOB fee is a separate dimension (not in the regular+state receipt gas) and is
  -- still added below. i = bv_mtx_skip_idx (tx index); eff_price in bv_fee_egp_scratch (live).
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t1, t1, 3\n" ++
  "  la t2, bvgr_receipt_gas_increments; add t2, t2, t1; ld a1, 0(t2)\n" ++   -- receipt_gas_used[i] (u64)
  "  la a0, bv_fee_egp_scratch; la a2, bv_b2_debit_out; addi a2, a2, 16\n" ++
  "  jal ra, u256_mul_u64_be\n" ++                                            -- debit = eff_price * gas_used
  "  bnez a0, .Lbv_b2_next\n" ++                                              -- overflow (unreachable for real values)
  "  la a0, bv_b2_debit_out; addi a0, a0, 16; la a1, bv_mtx_skip_ctx; addi a1, a1, 96; la a2, bv_b2_debit_out; addi a2, a2, 16\n" ++
  "  jal ra, u256_add_be\n" ++                                               -- debit += tx.value
  "  bnez a0, .Lbv_b2_next\n" ++
  ".Lbv_b2_after_value:\n" ++
  "  la t2, bv_mtx_skip_ctx; ld a0, 8(t2); ld a1, 16(t2); la a2, bv_b23_txtype; la a3, bv_b23_innoff\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  ".Lbv_b2_after_type4_auth:\n" ++
  "  la t0, bv_b23_txtype; ld t1, 0(t0); li t2, 3; bne t1, t2, .Lbv_b2_blob_done\n" ++
  "  la t2, bv_mtx_skip_ctx; ld t4, 16(t2); la t0, bv_b23_innoff; ld t3, 0(t0); bltu t4, t3, .Lbv_b2_next\n" ++
  "  la t2, bv_mtx_skip_ctx; ld t1, 8(t2); add a0, t1, t3; ld t4, 16(t2); sub a1, t4, t3; la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, bv_b23_innoff; ld t3, 0(t3); la t4, bv_mtx_skip_ctx; ld t4, 8(t4); add t3, t4, t3; add a0, t3, t1; mv a1, t2; la a2, bv_b23_blobcount\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  "  la t0, bv_b23_blobcount; ld a1, 0(t0); beqz a1, .Lbv_b2_next\n" ++
  "  li t2, 6; bgtu a1, t2, .Lbv_b2_next\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, bsg_blob_price_be; la a2, bv_b23_feedebit\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  "  la a0, bv_b2_debit_out; addi a0, a0, 16; la a1, bv_b23_feedebit; la a2, bv_b2_debit_out; addi a2, a2, 16\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  ".Lbv_b2_blob_done:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t3, t1, 6; la t4, bv_mtx_skip_list; add t4, t4, t3\n" ++
  "  la a0, bv_b2_table; la a1, bv_b2_count; li a2, " ++ toString bvMtxSenderBalanceEntries ++ "; mv a3, t4; la a4, bv_mtx_sender_acct; addi a4, a4, 8; la a5, bv_b2_debit_out; addi a5, a5, 16\n" ++
  "  jal ra, multi_tx_running_sender_balance_step\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_sender_upfront_fail\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  ".Lbv_b2_next:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_b2_loop\n" ++
  ".Lbv_b2_done:\n" ++
  -- bmvmx.5.5.2.2.3 (umbrella-B2.3): compare each distinct sender's running balance
  -- (pre - Σ actual debit, accumulated in bv_b2_table at +32) against the BAL-declared
  -- sender FINAL balance. This is the cumulative-balance generalization of the single-tx
  -- sender-post check (tx_gas_bal_post_verify_runtime, status 40): senders are excluded
  -- from the A2a all-accounts non-storage comparator (they sit in the A1 skip-list because
  -- their balance delta is gas/value-coupled, absent from the exec effect log), so this is
  -- the ONLY check that ties a multi-tx sender's BAL balance delta to the execution gas
  -- model. A forged sender post balance otherwise survives (the state-root recompute applies
  -- the BAL delta, so a matching forged header.state_root would pass).
  --
  -- The running balance models pre - Σ(receipt_inc*eff_price + tx.value) only. Do not
  -- skip sender==coinbase here: if the model omits the priority-fee credit, the mismatch
  -- must surface as a real B2.3 failure instead of being hidden by a post-fact bypass.
  -- We still conservatively skip senders whose final balance could include a frame-local
  -- value credit the debit model cannot distinguish yet:
  --   * effect-log overflow or any withdrawals present -> skip the whole pass (the exec
  --     effect log is then incomplete; mirrors the A2a guard below);
  --   * sender present in the exec non-storage effect log -> execution touched its balance
  --     (value-in via CALL, or value-out it sent) -> potential inbound credit not modeled.
  -- The remaining PURE-PAYER senders (the common multi-tx EOA case, value=0) must satisfy
  -- BAL_post == pre - Σdebit EXACTLY; a forged post balance rejects (.Lbv_mtx_sender_balance_fail,
  -- status 57). The running balance is u256 BE (u256_sub_be) and the BAL post is u256 BE
  -- right-aligned, so the 4-dword compare is byte-order aligned. Loop cursor lives in
  -- bv_mtx_skip_idx (memory) to survive the BAL-lookup jals; s0/s3 are callee-saved.
  "  la t0, exec_nonstorage_effect_overflow; ld t0, 0(t0); bnez t0, .Lbv_b23_done\n" ++
  "  la t0, svf_wds_count; ld t0, 0(t0); bnez t0, .Lbv_b23_done\n" ++
  -- (Type-3/4 txs are now debited exactly by the B2.2 loop's typed-fee addition above; a tx
  -- whose typed fee was inconclusive was skipped there and is absent from bv_b2_table, so no
  -- per-block tx-type pre-scan is needed here.)
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_b23_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_b2_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_b23_done\n" ++
  "  slli t3, t1, 6; la t4, bv_b2_table; add t4, t4, t3\n" ++   -- t4 = &entry (addr@0, running balance@32)
  -- Skip if sender appears in the raw exec non-storage effect log (112-byte records, addr@0)
  "  la t5, exec_nonstorage_effect_count; ld t5, 0(t5); li t6, 0\n" ++   -- t5 = raw count, t6 = k
  ".Lbv_b23_agg:\n" ++
  "  bgeu t6, t5, .Lbv_b23_chk\n" ++
  "  li a0, 112; mul a0, t6, a0; la a1, exec_nonstorage_effect_log; add a1, a1, a0; li a2, 0\n" ++  -- a1 = &log[k]
  ".Lbv_b23_agg_cmp:\n" ++
  "  li a3, 20; beq a2, a3, .Lbv_b23_next\n" ++                 -- 20/20 equal -> exec touched sender -> skip
  "  add a3, t4, a2; lbu a3, 0(a3); add a4, a1, a2; lbu a4, 0(a4); bne a3, a4, .Lbv_b23_agg_adv\n" ++
  "  addi a2, a2, 1; j .Lbv_b23_agg_cmp\n" ++
  ".Lbv_b23_agg_adv:\n" ++
  "  addi t6, t6, 1; j .Lbv_b23_agg\n" ++
  ".Lbv_b23_chk:\n" ++
  -- pure-payer sender: look up its BAL AccountChanges and compare the declared post balance.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0); mv a2, t4; la a3, bv_b1_acct_ptr; la a4, bv_b1_acct_len\n" ++
  "  jal ra, bal_find_account_by_address\n" ++
  "  bnez a0, .Lbv_b23_next\n" ++                               -- sender absent from BAL -> skip (conservative)
  "  la t0, bv_b1_acct_ptr; ld a0, 0(t0); la t0, bv_b1_acct_len; ld a1, 0(t0); la a2, bv_b1_finals\n" ++
  "  jal ra, bal_account_nonstorage_finals\n" ++
  "  bnez a0, .Lbv_b23_next\n" ++                               -- parse fail -> skip
  "  la t0, bv_b1_finals; ld t1, 0(t0); beqz t1, .Lbv_b23_next\n" ++  -- has_balance == 0 -> skip (no declared change)
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t3, t1, 6; la t4, bv_b2_table; add t4, t4, t3; addi t4, t4, 32\n" ++  -- t4 = &running (reload; jals clobbered)
  "  la t5, bv_b1_finals; addi t5, t5, 8\n" ++                  -- t5 = &BAL post balance (32B BE)
  "  ld a0, 0(t4); ld a1, 0(t5); bne a0, a1, .Lbv_mtx_sender_balance_fail\n" ++
  "  ld a0, 8(t4); ld a1, 8(t5); bne a0, a1, .Lbv_mtx_sender_balance_fail\n" ++
  "  ld a0, 16(t4); ld a1, 16(t5); bne a0, a1, .Lbv_mtx_sender_balance_fail\n" ++
  "  ld a0, 24(t4); ld a1, 24(t5); bne a0, a1, .Lbv_mtx_sender_balance_fail\n" ++
  ".Lbv_b23_next:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_b23_loop\n" ++
  ".Lbv_b23_done:\n" ++
  "  j .Lbv_mtx_b2_return\n" ++   -- bmvmx.5.5.2.2.12: relocated B2.2/B2.3 done -> return to ReceiptsTail (after the gas-result gate)
  ".Lbv_mtx_storage:\n" ++        -- storage/tuples/A2a run at .Lbv_mtx_done (B2 skipped there via the .Lbv_b1_done jump)
  -- bmvmx.5.5.1.2.1.2: all-accounts STORAGE exec-vs-BAL for the MULTI-TX path,
  -- storage-only slice. Reuse the A1 skip-list so every top-level sender/recipient plus
  -- coinbase is left to the gas/value path, while non-recipient nested-callee storage remains
  -- checked against the persistent execution storage log. Tuple-sequence wiring stays out of
  -- this slice so regressions are attributable to storage only.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  li a2, 0xa0630000\n" ++
  "  la t0, evm_env; ld a3, 448(t0)\n" ++
  "  la a4, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a5, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_storage_consistent_skip_list\n" ++
  "  bnez a0, .Lbv_bal_allaccounts_fail\n" ++
  -- bmvmx.5.5.1.2.1.3: tuple-sequence consistency over every non-skip BAL account
  -- in the multi-tx path. This mirrors the single-tx call while using the A1 skip-list.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  li a2, 0xa0630000\n" ++
  "  la t0, evm_env; ld a3, 448(t0)\n" ++
  "  la a4, exec_log_txindex\n" ++
  "  la a5, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a6, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_tuple_sequences_consistent_skip_list\n" ++
  "  bnez a0, .Lbv_bal_tuple_fail\n" ++
  -- bmvmx.5.5.1 (umbrella-A2a): all-accounts NON-STORAGE exec-vs-BAL for the MULTI-TX path
  -- (the single-tx comparators @1077-1094 were skipped by the @618 jump -> bmvmx.5.5). Wired
  -- here, consuming the A1 skip-list. CONSERVATIVE guard: effect-log overflow (skip -> never
  -- false-reject). NOTE (bmvmx.5.5.7.3): with nonstorageEffectLogCap = 32768 the overflow guard is
  -- now UNREACHABLE under the 200M block-gas envelope (cheapest record-producing op is a value-CALL
  -- at GAS_WARM_ACCESS+GAS_CALL_VALUE=10400 regular gas, so <= 200M/10400 ~= 19230 < 32768 raw
  -- records), so it no longer skips any in-scope block.
  -- bmvmx.5.5.9: the WITHDRAWALS skip is REMOVED. EIP-4895 withdrawal credits land in the BAL but
  -- not the tx-execution effect log; the prior `svf_wds_count -> skip` bailed the WHOLE nonstorage
  -- exec-vs-BAL check whenever the block had withdrawals, leaving non-withdrawal accounts (CALL-
  -- value callees / CREATE / SELFDESTRUCT) unchecked. That is unnecessary: withdrawal-recipient
  -- balances are independently validated by withdrawals_state_root (pre-state + amount, folded into
  -- the post-state root vs the header), and the FORWARD comparator still allows accounts
  -- that declare no non-storage change. So running the check with withdrawals present is
  -- 0-regress for valid blocks and ENFORCES the exec-vs-BAL consistency of every
  -- effect-having account in a withdrawals block.
  "  la t0, exec_nonstorage_effect_overflow; ld t0, 0(t0); bnez t0, .Lbv_mtx_ns_skip\n" ++
  -- Aggregate exec_nonstorage_effect_log per-account into exec_nonstorage_effect_agg, keyed by
  -- the 20B BE address @rec+0, keeping first-seen pre + last-seen post per account (BAL final ==
  -- exec post / net-change post!=pre). bmvmx.5.5.7.3: this was an inline O(raw*distinct) scan;
  -- now delegated to the O(20*N) stable-radix-sort + run-compress helper nonstorage_effect_aggregate
  -- (KAT-validated, zisk_nonstorage_effect_aggregate), so the effect-log cap can be lifted toward
  -- the 200M worst-case without a step-budget blowup. Same first-pre/last-post semantics; the
  -- output order differs (sorted vs first-seen) but bal_all_accounts_nonstorage_consistent scans
  -- the agg by address (order-independent). The helper resets agg_count and preserves s-regs.
  "  la a0, exec_nonstorage_effect_log; la t0, exec_nonstorage_effect_count; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_agg; la a3, exec_nonstorage_effect_agg_count; li a4, " ++ toString nonstorageEffectLogCap ++ "\n" ++
  "  jal ra, nonstorage_effect_aggregate\n" ++
  ".Lbv_agg_done:\n" ++
  -- forward: every non-skip BAL account's declared balance/nonce change is reproduced by exec.
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_agg; la t0, exec_nonstorage_effect_agg_count; ld a3, 0(t0)\n" ++
  "  la a4, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a5, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_nonstorage_consistent\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_fail\n" ++
  -- reverse (covers): every exec net-changed account is present in the BAL
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_agg; la t0, exec_nonstorage_effect_agg_count; ld a3, 0(t0)\n" ++
  "  la a4, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a5, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_nonstorage_covers\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_covers_fail\n" ++
  ".Lbv_mtx_ns_skip:\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"
