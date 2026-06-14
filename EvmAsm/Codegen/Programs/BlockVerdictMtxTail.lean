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

namespace EvmAsm.Codegen

/-- Multi-tx exec-vs-BAL validation tail of `block_verdict` (skip-list build + B1
    sender-nonce + A2a non-storage comparators), concatenated at .Lbv_mtx_done. -/
def blockVerdictMtxValidationTail : String :=
  -- bmvmx.5.5.1 (umbrella-A1): build the MULTI-TX skip-list that the all-accounts
  -- exec-vs-BAL comparators (@1032-1110, run only on the single-tx path today) must
  -- skip. The single-tx i3djw_skip_list is the fixed 3 entries {recipient, sender,
  -- coinbase}; a multi-tx block has up to 2N+1 such gas/value-coupled accounts. We are
  -- at .Lbv_mtx_done, so EVERY tx reached a status-0 supported shape -> re-deriving
  -- each is safe (address_from_pubkey already ran @474, multi_tx_nth_context @438):
  --   skip[2i]   = sender_i    = address_from_pubkey(public_keys[i]+1)   (as @473-474)
  --   skip[2i+1] = recipient_i = multi_tx_nth_context(bv_mtx_skip_ctx,i)+72 (pure re-extract)
  --   skip[2N]   = coinbase     = fee_recipient (bv_exec_p+32)            (as @161-164)
  -- count = 2N+1. 32-byte-strided, address in the first 20 bytes. BEHAVIOR-NEUTRAL:
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
  "  la t2, bv_tx_count; ld t2, 0(t2); slli t3, t2, 1; addi t3, t3, 1; la t0, bv_mtx_skip_count; sd t3, 0(t0)\n" ++  -- count = 2N+1
  -- bmvmx.5.5.2 (umbrella-B1): validate each multi-tx SENDER's BAL FINAL nonce == pre_nonce +
  -- (total count of that sender's txs) -- the multi-tx generalization of the single-tx post-
  -- nonce check (.Lbv_sender_nonce_fail, status 40). An EOA sender's nonce increments once per
  -- tx (no internal code), so final == pre+count for every valid block -> never false-rejects;
  -- catches a BAL forging the sender's final nonce. Post-loop pass; sender_i = skip[2i] (A1),
  -- compacted by b1_sender_count_table into distinct sender/count rows. Conservative skips:
  -- sender absent from BAL, account_at failure, no declared nonce change. Cursor in
  -- bv_mtx_skip_idx walks the distinct table and survives jals via memory.
  "  la a0, bv_mtx_skip_list; la t0, bv_tx_count; ld a1, 0(t0); la a2, bv_b1_sender_table; li a3, 16; la a4, bv_b1_sender_count\n" ++
  "  jal ra, b1_sender_count_table\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++                              -- impossible for tx_count <= 16; reject if table build failed
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
  -- bmvmx.5.5.2.2.2 (umbrella-B2.2): maintain a per-sender running
  -- balance table in tx order. This rejects only if actual post-exec debit
  -- underflows the sender running balance; final BAL-post comparison is B2.3.
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
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t1, t1, 3\n" ++
  "  la t2, bv_mtx_gas_left; add t2, t2, t1; ld a1, 0(t2)\n" ++
  "  la t2, bv_mtx_refund; add t2, t2, t1; ld a2, 0(t2)\n" ++
  "  la t2, bv_mtx_calldata; add t2, t2, t1; ld a3, 0(t2)\n" ++
  "  la a0, bv_mtx_skip_ctx; la a4, bv_fee_egp_scratch; la a5, bv_b2_debit_out\n" ++
  "  jal ra, multi_tx_actual_sender_debit\n" ++
  "  la t0, bv_b2_debit_out; ld t0, 0(t0); bnez t0, .Lbv_b2_next\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t3, t1, 6; la t4, bv_mtx_skip_list; add t4, t4, t3\n" ++
  "  la a0, bv_b2_table; la a1, bv_b2_count; li a2, 16; mv a3, t4; la a4, bv_mtx_sender_acct; addi a4, a4, 8; la a5, bv_b2_debit_out; addi a5, a5, 16\n" ++
  "  jal ra, multi_tx_running_sender_balance_step\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_sender_upfront_fail\n" ++
  "  bnez a0, .Lbv_b2_next\n" ++
  ".Lbv_b2_next:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_b2_loop\n" ++
  ".Lbv_b2_done:\n" ++
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
  -- bmvmx.5.5.1 (umbrella-A2a): all-accounts NON-STORAGE exec-vs-BAL for the MULTI-TX path
  -- (the single-tx comparators @1077-1094 were skipped by the @618 jump -> bmvmx.5.5). Wired
  -- here, consuming the A1 skip-list. CONSERVATIVE guards (skip -> never false-reject, like the
  -- gas-path wds guard @1174): (a) effect-log overflow (64-cap dropped records); (b) withdrawals
  -- (system-level credits land in the BAL but not the tx-execution effect log). Both -> skip.
  "  la t0, exec_nonstorage_effect_overflow; ld t0, 0(t0); bnez t0, .Lbv_mtx_ns_skip\n  la t0, svf_wds_count; ld t0, 0(t0); bnez t0, .Lbv_mtx_ns_skip\n" ++
  -- Aggregate exec_nonstorage_effect_log per-account into exec_nonstorage_effect_agg, keyed by
  -- the 20B BE address @rec+0: first-seen record copied whole; a later record for the same
  -- account overwrites only post_balance (+64,32B) + post_nonce (+104,8B). Records append in
  -- tx/exec order -> kept pre = block-start, kept post = block-final (what the comparator wants;
  -- BAL final == exec post / net-change post!=pre). The count never resets across the block in
  -- the real path (only the probe @130 zeroes it). Pure loop (no calls -> counters in t/a regs).
  "  la t0, exec_nonstorage_effect_agg_count; sd zero, 0(t0)\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); li t2, 0\n" ++   -- t1 = raw count, t2 = j
  ".Lbv_agg_loop:\n" ++
  "  bgeu t2, t1, .Lbv_agg_done\n" ++
  "  li t3, 112; mul t3, t2, t3; la t4, exec_nonstorage_effect_log; add t4, t4, t3\n" ++   -- t4 = &log[j]
  "  la t5, exec_nonstorage_effect_agg_count; ld t5, 0(t5); li t6, 0\n" ++   -- t5 = agg_count, t6 = k
  ".Lbv_agg_scan:\n" ++
  "  bgeu t6, t5, .Lbv_agg_append\n" ++
  "  li a0, 112; mul a0, t6, a0; la a1, exec_nonstorage_effect_agg; add a1, a1, a0; li a2, 0\n" ++   -- a1 = &agg[k]
  ".Lbv_agg_cmp:\n" ++
  "  li a3, 20; beq a2, a3, .Lbv_agg_update\n" ++
  "  add a4, t4, a2; lbu a5, 0(a4); add a4, a1, a2; lbu a6, 0(a4); bne a5, a6, .Lbv_agg_scan_adv\n" ++
  "  addi a2, a2, 1; j .Lbv_agg_cmp\n" ++
  ".Lbv_agg_scan_adv:\n" ++
  "  addi t6, t6, 1; j .Lbv_agg_scan\n" ++
  ".Lbv_agg_update:\n" ++   -- agg[k] = a1: overwrite post_balance (+64,32B) + post_nonce (+104,8B) from log[j]
  "  ld a2, 64(t4); sd a2, 64(a1); ld a2, 72(t4); sd a2, 72(a1); ld a2, 80(t4); sd a2, 80(a1); ld a2, 88(t4); sd a2, 88(a1); ld a2, 104(t4); sd a2, 104(a1)\n" ++
  "  j .Lbv_agg_next\n" ++
  ".Lbv_agg_append:\n" ++   -- copy full 112B log[j] -> agg[agg_count]; agg_count++
  "  li a0, 112; mul a0, t5, a0; la a1, exec_nonstorage_effect_agg; add a1, a1, a0; li a2, 0\n" ++
  ".Lbv_agg_copy:\n" ++
  "  li a3, 112; beq a2, a3, .Lbv_agg_copy_d\n" ++
  "  add a4, t4, a2; lbu a5, 0(a4); add a4, a1, a2; sb a5, 0(a4); addi a2, a2, 1; j .Lbv_agg_copy\n" ++
  ".Lbv_agg_copy_d:\n" ++
  "  addi t5, t5, 1; la a0, exec_nonstorage_effect_agg_count; sd t5, 0(a0)\n" ++
  ".Lbv_agg_next:\n" ++
  "  addi t2, t2, 1; j .Lbv_agg_loop\n" ++
  ".Lbv_agg_done:\n" ++
  -- forward: every non-skip BAL account's declared balance/nonce change is reproduced by exec.
  -- LENIENT mode (c3ns_lenient_notfound=1): a multi-tx block may still have created-account
  -- effects outside the CALL zero-pre path, so strict notfound remains gated until those are
  -- complete. Value-mismatch still validates every account that DID get an effect. Reset to 0
  -- after so nothing else observes lenient mode.
  "  la t0, c3ns_lenient_notfound; li t1, 1; sd t1, 0(t0)\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_agg; la t0, exec_nonstorage_effect_agg_count; ld a3, 0(t0)\n" ++
  "  la a4, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a5, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_nonstorage_consistent\n" ++
  "  la t0, c3ns_lenient_notfound; sd zero, 0(t0)\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_fail\n" ++
  -- reverse (covers): every exec net-changed account is present in the BAL
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  la a2, exec_nonstorage_effect_agg; la t0, exec_nonstorage_effect_agg_count; ld a3, 0(t0)\n" ++
  "  la a4, bv_mtx_skip_list; la t0, bv_mtx_skip_count; ld a5, 0(t0)\n" ++
  "  jal ra, bal_all_accounts_nonstorage_covers\n" ++
  "  bnez a0, .Lbv_bal_nonstorage_covers_fail\n" ++
  ".Lbv_mtx_ns_skip:\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"

