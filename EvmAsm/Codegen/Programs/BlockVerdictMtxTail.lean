/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxTail

  Multi-tx validation tail of block_verdict (the .Lbv_mtx_done block: A1 skip-list
  builder, B2 running-balance underflow, map↔builder DIR A). B1/B2.3 BAL
  field compares retired #11183 ORDER-1. Pure asm-string fragment.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.AmsterdamSystemTx
import EvmAsm.Codegen.Programs.NonstorageEffectLog

namespace EvmAsm.Codegen

/-- Multi-tx validation tail of `block_verdict` (skip-list + B2.2 + map check). -/
def blockVerdictMtxValidationTail : String :=
  -- bmvmx.5.5.1 (umbrella-A1): build the MULTI-TX skip-list that the all-accounts
  -- exec-vs-BAL storage/tuple/nonstorage comparators must skip. Gas/value-coupled
  -- accounts ONLY — no system addresses (#10684 / #11210 / #11218 union: all six
  -- system whole-account skips are FA surfaces with no execution-specs counterpart).
  -- At .Lbv_mtx_done every tx reached a status-0 supported shape -> re-deriving safe:
  --   skip[2i]   = sender_i    = address_from_pubkey(public_keys[i]+1)
  --   skip[2i+1] = effective recipient_i = the dispatch-settled target
  --                 (raw recipient for CALL/EOA, derived CREATE address for creation)
  --   skip[2N]   = coinbase     = fee_recipient (bv_exec_p+32)
  -- count = 2N+1. 32-byte-strided, address in the first 20 bytes. The build loop's
  -- cursor lives in bv_mtx_skip_idx (memory) so it survives the jal calls; s0/s3
  -- are callee-saved and preserved across them.
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_skl_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_skl_done\n" ++
  "  slli t3, t1, 6; add t4, t3, t1\n" ++                               -- t4 = i*65
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t4; addi a0, t0, 1\n" ++  -- a0 = public_keys[i]+1 (skip 0x04)
  "  slli t5, t1, 6; la a1, bv_mtx_skip_list; add a1, a1, t5\n" ++      -- a1 = &skip[2i] (offset i*64)
  "  jal ra, address_from_pubkey\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t5, t1, 6; addi t5, t5, 32\n" ++
  "  la t6, bv_mtx_skip_list; add t6, t6, t5\n" ++                      -- t6 = &skip[2i+1] (offset i*64+32)
  "  la t2, bv_mtx_skip_idx; ld t1, 0(t2); slli t1, t1, 5; la t2, bv_mtx_effective_recipient_table; add t2, t2, t1; li t3, 0\n" ++ -- src = effective recipient
  ".Lbv_skl_rcopy:\n  li t4, 20; beq t3, t4, .Lbv_skl_rcopy_d\n  add t4, t2, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4); addi t3, t3, 1; j .Lbv_skl_rcopy\n.Lbv_skl_rcopy_d:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_skl_loop\n" ++
  ".Lbv_skl_done:\n" ++
  "  la t2, bv_tx_count; ld t2, 0(t2); slli t5, t2, 6; la t6, bv_mtx_skip_list; add t6, t6, t5\n" ++  -- t6 = &skip[2N] (offset N*64)
  "  la t1, bv_exec_p; ld t1, 0(t1); addi t1, t1, 32; li t3, 0\n" ++    -- src = fee_recipient (exec_p+32)
  ".Lbv_skl_cb:\n  li t4, 20; beq t3, t4, .Lbv_skl_cb_d\n  add t4, t1, t3; lbu a0, 0(t4); add t4, t6, t3; sb a0, 0(t4); addi t3, t3, 1; j .Lbv_skl_cb\n.Lbv_skl_cb_d:\n" ++
  -- #10684/#11210/#11218: NO system copy. count = 2N+1 only (senders+recipients+coinbase).
  "  la t2, bv_tx_count; ld t2, 0(t2); slli t3, t2, 1; addi t3, t3, 1; la t0, bv_mtx_skip_count; sd t3, 0(t0)\n" ++
  -- #11183 ORDER-1: RETIRED B1 BAL final-nonce field compare (.Lbv_b1_loop Class-A).
  -- Spec pin e5a8caf1b fork.py:390 — only hash of BUILT BAL vs header. Spec has no
  -- supplied body and no field compare; guest field-compare is FR under collision
  -- (equivalence, not "hash covers it"). Fail sink .Lbv_mtx_sender_final_nonce_fail
  -- remains labelled dead in ReceiptsTail until unlinked.
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
  -- A reverted / exceptional transaction still pays gas, but its call value is
  -- rolled back.  `bv_tx_status_arr[i]` is the authoritative settle status
  -- published by the MTx runtime, so add value only for a committed body.  A
  -- committed transfer to self also retains its value: sender and recipient
  -- are the same AccountState entry, so only the gas/blob debit is netted.
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t1, t1, 3; la t0, bv_tx_status_arr; add t0, t0, t1; ld t0, 0(t0); beqz t0, .Lbv_b2_after_value\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); slli t1, t1, 6; la t2, bv_mtx_skip_list; add t2, t2, t1; addi t3, t2, 32; li t4, 20\n" ++
  ".Lbv_b2_self_value_cmp:\n" ++
  "  beqz t4, .Lbv_b2_after_value\n" ++
  "  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbv_b2_add_value\n" ++
  "  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lbv_b2_self_value_cmp\n" ++
  ".Lbv_b2_add_value:\n" ++
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
  -- #11183 ORDER-1: RETIRED B2.3 BAL post-balance field compare (.Lbv_b23_chk Class-A).
  -- Spec pin e5a8caf1b fork.py:390 — only hash of BUILT BAL vs header. Spec has no
  -- supplied body and no field compare; guest field-compare is FR under collision
  -- (equivalence, not "hash covers it"). B2.2 running-balance underflow (exec model)
  -- KEPT above. Fail sink .Lbv_mtx_sender_balance_fail remains labelled dead until unlinked.
  ".Lbv_b23_done:\n" ++
  "  j .Lbv_mtx_b2_return\n" ++   -- bmvmx.5.5.2.2.12: B2.2 done -> return to ReceiptsTail
  ".Lbv_mtx_storage:\n" ++
  -- #10612 / #11245: retire granular BAL field stand-ins that the survivor hash
  -- already covers. Spec pin e5a8caf1b amsterdam fork.py:366 + :390 — one
  -- hash_block_access_list vs header. Guest survivor: bal_serializer_verify
  -- bound ACCEPT-only → bv_fail 60/61 (ReceiptsTail).
  --
  -- RETIRED here (hash subsumes the BAL bytes these inspected):
  --   bal_all_accounts_storage_consistent_skip_list  (code 37)
  --   bal_all_accounts_nonstorage_consistent         (code 44)
  --   bal_all_accounts_nonstorage_covers              (code 45)
  --   plus the nonstorage_effect_aggregate prep that fed 44/45 only
  --   bal_all_accounts_tuple_sequences_consistent_skip_list (code 42)
  --     — #10646 CLOSED then #11666 RETIRED: exclusive callee chain deleted
  --       (account/slot/exec_log tuple helpers + capture_system_storage_exec_rows
  --       + bv_system_storage_txindex). bv_mtx_skip_list KEPT — still feeds B1/B2.
  -- #11183 DIR A only: map finals ↔ highest-BAI builder (guest-internal fail-safe).
  -- DIR B/C (supplied BAL body) dropped — serialised fields ⊆ hash 60/61.
  -- No bv_bal_start/len: not a Class-A edge. Code 66 on map↔builder desync.
  "  jal ra, bal_map_builder_consistent\n" ++
  "  bnez a0, .Lbv_bal_map_fail\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"
