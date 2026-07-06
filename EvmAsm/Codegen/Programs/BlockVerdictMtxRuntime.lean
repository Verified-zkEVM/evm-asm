/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxRuntime

  Extracted multi-transaction runtime-gas fragment for block_verdict.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictMtxTail
import EvmAsm.Codegen.Programs.BlockVerdictMtxEoa
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate
import EvmAsm.Codegen.Programs.BlockVerdictMtxCoinbase
import EvmAsm.Codegen.Programs.CommittedStorageSnapshot

namespace EvmAsm.Codegen

/-- Gated multi-transaction runtime-gas loop fragment, ending before `.Lbv_singletx`. -/
def blockVerdictMtxRuntimeLoop : String :=
  -- evm-asm-fhsxz.2.4.2.57.11.6.2.2.2: gated multi-transaction runtime gas loop.
  -- tx_count==1 (and the degenerate 0-tx block) fall through to the existing
  -- single-tx path BYTE-IDENTICALLY. For 2..16 transactions, only when the block
  -- is INDEPENDENT (bal_txs_independent==0: no account's storage/code/nonce touched
  -- by more than one tx_index) AND every recipient is a self-contained contract,
  -- dispatch each tx against the block-PRE state to measure its runtime gas,
  -- populate the strided runtime-result arrays, and set bvgr_runtime_count=tx_count
  -- so block_verdict_gas_result_arena_prepare + the EIP-7778/8037 block-gas gate
  -- run. Independence makes per-tx pre-state dispatch exact; the per-tx refund is
  -- read from evm_refund_acc (the dispatcher's EIP-3529 SSTORE refund accumulator,
  -- reset per dispatch) so the receipt-gas increment (receipt_inc) is exact; the
  -- EIP-7778 block-gas gate stays refund-independent (block_inc). Any non-independence / unsupported
  -- tx shape / EOA recipient / dispatch miss bails to the conservative path
  -- (bvgr_runtime_count left 0 -> arena count mismatch -> block-gas gate skipped),
  -- i.e. today's behavior, so valid multi-tx blocks are never newly false-rejected.
  "  la t0, bv_tx_count; ld t0, 0(t0); li t1, 1; beq t0, t1, .Lbv_singletx\n" ++
  "  li t1, 2; bltu t0, t1, .Lbv_singletx          # 0-tx block -> existing path\n" ++
  "  li t1, " ++ toString bvMtxActiveTxCap ++ "; bgtu t0, t1, .Lbv_mtx_bail         # active loop capacity\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  bnez a0, .Lbv_mtx_bail                         # interacting / parse error -> conservative\n" ++
  -- Build the sorted sender index once from public keys. The exact per-tx nonce
  -- check below binary-searches this table and mutates the count field as the
  -- running prior-seen count; the B1 final-nonce tail rebuilds totals later.
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_mtx_sender_seed_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_mtx_sender_seed_done\n" ++
  "  slli t3, t1, 6; add t4, t3, t1\n" ++
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t4; addi a0, t0, 1\n" ++
  "  slli t5, t1, 6; la a1, bv_mtx_skip_list; add a1, a1, t5\n" ++
  "  jal ra, address_from_pubkey\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_sender_seed_loop\n" ++
  ".Lbv_mtx_sender_seed_done:\n" ++
  "  la a0, bv_mtx_skip_list; la t0, bv_tx_count; ld a1, 0(t0); la a2, bv_b1_sender_table; li a3, " ++ toString bvMtxSenderCountEntries ++ "; la a4, bv_b1_sender_count\n" ++
  "  jal ra, b1_sender_count_table\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_mtx_sender_count_zero_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_b1_sender_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_mtx_sender_count_zero_done\n" ++
  "  li t3, 40; mul t3, t1, t3; la t4, bv_b1_sender_table; add t4, t4, t3; sd zero, 32(t4)\n" ++
  "  addi t1, t1, 1; la t0, bv_mtx_skip_idx; sd t1, 0(t0); j .Lbv_mtx_sender_count_zero_loop\n" ++
  ".Lbv_mtx_sender_count_zero_done:\n" ++
  "  la t0, bv_mtx_i; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_committed_count; sd zero, 0(t0); la t0, bv_mtx_committed_overflow; sd zero, 0(t0)  # empty legacy cross-tx committed table/status\n" ++
  "  la t0, bv_mtx_committed_chunk_count; sd zero, 0(t0); la t0, bv_mtx_committed_chunk_overflow; sd zero, 0(t0)  # empty chunked cross-tx committed table/status\n" ++
  -- bmvmx.5 (fee-validity hoist, multi-tx): multi_tx_nth_context does NOT populate the
  -- record's base_fee_per_gas (record+32 is a per-call INPUT, BlockVerdictMultiTx.lean:44),
  -- so compute the BLOCK base_fee once here (it is block-level, identical for every tx) by
  -- reversing the payload's SSZ little-endian base_fee at bv_exec_p+440 into BE
  -- (bv_mtx_base_fee_be), mirroring the single-tx envelope reversal at line ~101. The per-tx
  -- fee gate below points tx_effective_gas_pricing's a2 at this buffer. bv_exec_p was set
  -- unconditionally at line ~77 (before the tx-count split), so it is valid here.
  "  la t4, bv_exec_p; ld t4, 0(t4); addi t1, t4, 440; la t2, bv_mtx_base_fee_be; li t3, 0\n" ++
  ".Lbv_mtx_bf_rev:\n" ++
  "  li t0, 32; beq t3, t0, .Lbv_mtx_bf_rev_done\n" ++
  "  add t0, t1, t3; lbu t5, 0(t0); li t6, 31; sub t6, t6, t3; add t6, t2, t6; sb t5, 0(t6); addi t3, t3, 1; j .Lbv_mtx_bf_rev\n" ++
  ".Lbv_mtx_bf_rev_done:\n" ++
  ".Lbv_mtx_loop:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); beq t1, t2, .Lbv_mtx_done\n" ++
  "  la a0, bv_mtx_ctx; mv a1, t1; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_ctx; ld t2, 0(t0); bnez t2, .Lbv_mtx_bail; ld t2, 48(t0); bnez t2, .Lbv_mtx_creation_unsupported        # creation tx shape\n" ++
  -- bmvmx.5 (fee-validity hoist, multi-tx): same PATH-INDEPENDENT check_transaction
  -- fee-validity test as the single-tx gate (max_fee>=base_fee / priority<=max_fee),
  -- run per tx in the mtx loop. bv_mtx_ctx holds tx ptr@8 / len@16 (simple_transfer layout,
  -- BlockVerdictMultiTx.lean:38); base_fee comes from bv_mtx_base_fee_be (computed above —
  -- record+32 is NOT filled by multi_tx_nth_context). Placed before the contract/EOA-recipient
  -- routing so it covers EVERY status-0 tx the loop reaches. tx_effective_gas_pricing returns
  -- 2 (priority>max_fee) / 3 (max_fee<base_fee) for the two spec errors; status 1 (extraction
  -- failed) / 4 (egp overflow) -> fall through. An invalid-fee tx is spec-rejected regardless
  -- of recipient type, and a valid block never carries one, so this only ADDS spec-faithful
  -- rejects -- no false-reject. (t1 is reset at the code-hash compare / reloaded from bv_mtx_i
  -- later; s0-s3 preserved by the call.)
  "  la t2, bv_mtx_ctx\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); la a2, bv_mtx_base_fee_be\n" ++   -- tx ptr, tx len, block base_fee (BE)
  "  la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  li t1, 2; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- priority_fee > max_fee -> reject
  "  li t1, 3; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- max_fee < base_fee -> reject
  -- bmvmx.5 (multi-tx nonce lower-bound, path-independent like the fee check above): the
  -- single-tx @1082 nonce check (tx.nonce == sender_pre_nonce) does NOT cover the mtx loop, so a
  -- multi-tx block carrying a tx whose nonce is BELOW the sender's pre-state nonce is currently
  -- accepted (the spec rejects it, NonceMismatchError). SOUND-PARTIAL check: reject if
  -- tx.nonce < sender_pre_nonce. Valid txs always have nonce >= the account's block-start nonce
  -- (==pre for the sender's first tx, >pre for a sequenced later tx), so this NEVER false-rejects;
  -- it catches the below-pre adversarial case; the running-count check below also rejects nonce reuse and too-high nonces.
  -- sttc_nonce holds THIS tx's nonce (multi_tx_nth_context wrote it via tx_extract_nonce_and_gas).
  -- sender = address_from_pubkey(public_keys[i]+1): public_keys[i] = bv_public_keys_ptr + i*65
  -- (65-byte SEC1 0x04||x||y, verified bound to tx[i]'s signer by verify_public_keys_match_senders).
  -- i*65 = (i<<6)+i. account_at_header_state_root(pre-state) -> sender acct, nonce@0. s0+8/16/80/88
  -- are the same lookup args the legacy sender lookup uses (@128). Lookup fail/absent -> skip
  -- (conservative; an absent sender has pre_nonce 0 and tx.nonce>=0, so the check is a no-op anyway).
  "  la t0, bv_mtx_i; ld t1, 0(t0)\n" ++
  "  slli t2, t1, 6; add t1, t2, t1\n" ++                       -- t1 = i*65
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t1; addi a0, t0, 1\n" ++  -- a0 = public_keys[i]+1 (skip 0x04)
  "  la a1, bv_mtx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_sender_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_mtx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_nonce_done\n" ++                         -- sender lookup failed/absent -> skip
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0)\n" ++              -- t0 = sender block-start (pre-state) nonce
  -- EXACT multi-tx nonce: tx.nonce must == pre_nonce + the running count already seen for
  -- this sender address in the current block. The pre-loop sender index is sorted, so each
  -- tx does a bounded binary lookup and increments that sender's running count in place.
  -- Sound: valid blocks sequence each sender's txs as pre,pre+1,...
  "  la t1, bv_mtx_nonce_pre; sd t0, 0(t1)\n" ++                -- stash pre_nonce across table lookup
  "  la a0, bv_b1_sender_table; la t2, bv_b1_sender_count; ld a1, 0(t2); la a2, bv_mtx_sender_addr\n" ++
  "  jal ra, b1_sender_table_find\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  mv t6, a1; ld t5, 32(t6); addi a0, t5, 1; sd a0, 32(t6)\n" ++
  "  la t0, bv_mtx_nonce_pre; ld t0, 0(t0)\n" ++
  "  add t0, t0, t5\n" ++                                       -- t0 = expected = pre_nonce + count
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                      -- t1 = tx.nonce
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                   -- tx.nonce != pre+count -> reject (Nonce*Error)
  -- bmvmx.5 (multi-tx upfront-balance lower bound): reject if sender_pre_balance <
  -- gas_limit*max_fee_per_gas + blob_gas*max_fee_per_blob_gas + tx.value (spec check_transaction InsufficientBalanceError,
  -- amsterdam fork.py). Mirrors the single-tx upfront check @1123-1138, swapping the operands to
  -- the mtx sources: max_fee = tefgp_max_fee (tx_effective_gas_pricing wrote it at @453 above),
  -- gas_limit = bv_mtx_ctx+40, value = bv_mtx_ctx+96 (multi_tx_nth_context simple_transfer layout),
  -- pre_balance = bv_mtx_sender_acct+8 (32B BE, from the account_at lookup just done). SOUND, no
  -- false-reject: a valid tx's sender covers its upfront (>= for the first tx, strictly > for a
  -- sequenced later tx), so pre_balance < upfront only for the definitely-insufficient case.
  -- (Exact per-sender prior-debit accounting is the sequencing follow-up; this lower bound holds
  -- without it.) Reuses the bv_upfront_cost/islt scratch; u256_mul_u64_be/add_be return 1 on
  -- overflow (a*b or sum >= 2^256 -> upfront unaffordable -> reject); u256_lt_be writes 1 iff a<b.
  "  la a0, tefgp_max_fee\n" ++
  "  la t0, bv_mtx_ctx; ld a1, 40(t0)\n" ++                     -- gas_limit (u64)
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++                    -- gas_limit*max_fee >= 2^256 -> reject
  "  la a0, bv_upfront_cost\n" ++
  "  la t0, bv_mtx_ctx; addi a1, t0, 96\n" ++                   -- tx.value (32B BE)
  "  la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++                    -- upfront + value >= 2^256 -> reject
  "  la t0, bv_mtx_ctx; ld t1, 160(t0); li t2, 3; bne t1, t2, .Lbv_mtx_upfront_blob_done\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); la a2, tcbg_struct\n" ++
  "  jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0)\n" ++
  "  la t3, bv_mtx_ctx; ld t3, 176(t3); add a0, t3, t1; mv a1, t2; la a2, bv_upfront_blob_count\n" ++
  "  jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la t0, bv_upfront_blob_count; ld a1, 0(t0); beqz a1, .Lbv_sender_upfront_fail\n" ++
  "  li t2, 6; bgtu a1, t2, .Lbv_sender_upfront_fail\n" ++
  "  slli a1, a1, 17\n" ++
  "  la a0, tcbg_blob_fee_be; la a2, bv_upfront_blob_cost\n" ++
  "  jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  "  la a0, bv_upfront_cost; la a1, bv_upfront_blob_cost; la a2, bv_upfront_cost\n" ++
  "  jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_sender_upfront_fail\n" ++
  ".Lbv_mtx_upfront_blob_done:\n" ++
  "  la a0, bv_mtx_sender_acct; addi a0, a0, 8\n" ++            -- sender pre_balance (32B BE)
  "  la a1, bv_upfront_cost\n" ++
  "  la a2, bv_upfront_islt\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, bv_upfront_islt; ld t0, 0(t0)\n" ++
  "  bnez t0, .Lbv_sender_upfront_fail\n" ++                    -- pre_balance < upfront -> reject
  ".Lbv_mtx_nonce_done:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_ctx; addi a2, a2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  -- fhsxz.2.4.2.57.11.6.5.4 (e): code 2 = MPT could not resolve this tx's recipient at the
  -- pre-state root. The recipient is ACCESSED (the tx sends to it), so a complete stateless
  -- witness MUST carry it -> code 2 means the witness genuinely lacks a node on its path
  -- (verified: the multi_transaction_gas_accounting GAS_USED_OVERFLOW witness omits tx1's
  -- recipient node, 22 vs the valid variant's 24 nodes). An unverifiable accessed account =>
  -- the block cannot be statelessly validated as valid => REJECT (not conservative-accept,
  -- which was the false-accept). A valid block's witness always resolves the recipient
  -- (code 0), so this never false-rejects. Codes 3/4 (decode/header) stay conservative.
  "  li t1, 2; beq a0, t1, .Lbv_mtx_recipient_unresolvable_fail\n" ++
  "  bnez a0, .Lbv_mtx_bail                         # other lookup failure (3/4) -> conservative\n" ++
  "  la t0, bv_tx_recipient_code_hash; la t1, chahsr_empty_code_hash\n" ++
  "  ld t3,  0(t0); ld t4,  0(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3,  8(t0); ld t4,  8(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3, 16(t0); ld t4, 16(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  ld t3, 24(t0); ld t4, 24(t1); bne t3, t4, .Lbv_mtx_is_contract\n" ++
  "  la t0, bv_mtx_ctx; addi a0, t0, 72; ld a1, 80(s0); ld a2, 88(s0); li a3, 0\n" ++
  "  jal ra, bal_same_block_delegation_code_resolve\n" ++
  "  beqz a0, .Lbv_mtx_is_contract\n" ++
  blockVerdictMtxEoaSettlement ++
  ".Lbv_mtx_is_contract:\n" ++
  -- bmvmx.1.6.6 multi-tx enabler: stamp this user tx's block_access_index = i+1 (EIP-7928:
  -- 0 for system, i+1 for the i-th user tx; fork.py:1030) so the SSTORE handler tags every
  -- exec-log entry it appends during this dispatch with the right per-tx index. Without this
  -- the loop leaves current_block_access_index at its single-tx default 1, and the per-tx
  -- tuple-sequence comparators (bmvmx.1.6.6) would see tx i>0 writes mis-indexed as 1.
  -- Additive/inert today: exec_log_txindex is consumed only by those (still-unwired) checks.
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  -- fhsxz.2.4.2.57.11.6.5: gate the PRE-state header to THIS (mtx) dispatch call only.
  -- Single-tx dispatch (.Lbv_cd_* path, line ~717) leaves the flag 0 -> sv_this_rlp,
  -- byte-identical to #8686 (no >10% regression recurrence). Reset immediately after.
  "  li t0, 1; la t1, dtrc_use_pre_header; sd t0, 0(t1)\n" ++
  -- bmvmx.7.2: multi-tx contract-recipient top-level EIP-7708 value-transfer log.
  -- Emit before runtime dispatch so the block log window preserves spec order: top-level
  -- value move first, then logs produced by the recipient code. If append overflows, leave
  -- the completeness flag unset and let the receipts gate stay conservative.
  "  la t0, bv_mtx_ctx; addi t0, t0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_mtx_tl7708_skip\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_tl_selfcmp:\n" ++
  "  beqz t2, .Lbv_mtx_tl7708_skip\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_tl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_tl_selfcmp\n" ++
  ".Lbv_mtx_tl_notself:\n" ++
  "  addi sp, sp, -16\n  sd x20, 0(sp)\n" ++
  "  la t0, eip7708_tl_from32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_sender_addr; addi t1, t1, 19; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_tl_from:\n  beqz t3, .Lbv_mtx_tl_from_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_from\n" ++
  ".Lbv_mtx_tl_from_d:\n" ++
  "  la t0, eip7708_tl_to32\n  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)\n" ++
  "  la t1, bv_mtx_ctx; addi t1, t1, 91; mv t2, t0; li t3, 20\n" ++
  ".Lbv_mtx_tl_to:\n  beqz t3, .Lbv_mtx_tl_to_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_to\n" ++
  ".Lbv_mtx_tl_to_d:\n" ++
  "  la t0, eip7708_tl_val32\n  la t1, bv_mtx_ctx; addi t1, t1, 127; mv t2, t0; li t3, 32\n" ++
  ".Lbv_mtx_tl_val:\n  beqz t3, .Lbv_mtx_tl_val_d\n  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_tl_val\n" ++
  ".Lbv_mtx_tl_val_d:\n" ++
  "  la x20, evm_env\n  la a0, eip7708_tl_from32\n  la a1, eip7708_tl_to32\n  la a2, eip7708_tl_val32\n" ++
  "  jal ra, eip7708_append_transfer_log\n" ++
  "  ld x20, 0(sp)\n  addi sp, sp, 16\n" ++
  "  bnez a0, .Lbv_mtx_tl7708_skip\n" ++
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_tl7708_skip:\n" ++
  -- bbow4.8: snapshot per-tx exec effect logs before the multi-tx runtime
  -- dispatch. A top-level tx that reverts/aborts discards its value-transfer /
  -- CREATE effects; child frames roll themselves back via frame_return, but the
  -- depth-0 tx exit path needs the same truncation as the single-tx path.
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); la t0, bv_tx_effect_snap_ns_count; sd t1, 0(t0)\n" ++
  "  la t0, exec_nonstorage_effect_overflow; ld t1, 0(t0); la t0, bv_tx_effect_snap_ns_overflow; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_count; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_count; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_next; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_next; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_overflow; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_overflow; sd t1, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; ld a1, 80(s0); ld a2, 88(s0); jal ra, dispatch_tx_runtime_code\n" ++
  "  la t0, bv_dispatch_runtime_status; sd a0, 0(t0)\n  la t1, dtrc_use_pre_header; sd zero, 0(t1)\n" ++
  "  bnez a0, .Lbv_mtx_dispatch_unsupported                         # structured dispatch bail reason\n" ++
  bvReceiptsShapeSet 5 true ++  -- fhsxz.2.4.2.57.11.6.5.2.1 P1: persist this tx's executed state gas into bvgr_tx_exec_state_gas[i]
  -- (i = bv_mtx_i; evm_state_gas_used is fresh per-tx). Clobbers only a0/t0-t2, preserves the dispatch
  -- results a1-a4 used below. Behavior-neutral substrate (array not yet read by the gate).
  "  la a0, bv_mtx_i; ld a0, 0(a0); jal ra, dispatcher_capture_exec_state_gas\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t0, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t0; sd a1, 0(t3)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t0; sd a2, 0(t3)\n" ++
  -- nxio8: a3 = the settle-folded refund counter (0 when the tx erred), not a
  -- raw evm_refund_acc read.
  "  la t3, bv_mtx_refund;   add t3, t3, t0; sd a3, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t0; sd a4, 0(t3)\n" ++   -- .63.1.6.2.1: receipt status, tx i
  "  la t3, bv_tx_is_creation_arr; add t3, t3, t0; la t4, bv_mtx_ctx; ld t5, 48(t4); sd t5, 0(t3)\n" ++
  "  slli t4, t1, 4\n" ++   -- .63.1.6.2.1: per-tx log window (16-byte stride)
  "  la t3, bv_tx_log_window; add t3, t3, t4\n" ++
  "  la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3)\n" ++
  "  la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  bnez a4, .Lbv_mtx_effects_kept\n" ++
  "  la t0, bv_tx_effect_snap_ns_count; ld t1, 0(t0); la t0, exec_nonstorage_effect_count; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_ns_overflow; ld t1, 0(t0); la t0, exec_nonstorage_effect_overflow; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_code_count; ld t1, 0(t0); la t0, exec_code_effect_count; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_code_next; ld t1, 0(t0); la t0, exec_code_effect_next; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_code_overflow; ld t1, 0(t0); la t0, exec_code_effect_overflow; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_effects_kept:\n" ++
  -- fhsxz.2.4.2.57.11.6.3.2: snapshot this tx's committed storage into the cross-tx table,
  -- re-keyed to its recipient so the next tx's preload can thread prior committed values.
  -- Duplicate (recipient, slotKey) writes update in place; only new unique keys consume capacity.
  "  la a0, bv_mtx_ctx; addi a0, a0, 72             # recipient key\n" ++
  "  li a1, 0xa0630000                              # live storage log base\n" ++
  "  la t0, evm_env; ld a2, 448(t0)                 # live log entry count\n" ++
  "  la a3, bv_mtx_committed_chunked; la t0, bv_mtx_committed_chunk_count; ld a4, 0(t0)\n" ++
  "  li a5, " ++ toString bvMtxCommittedChunkCapacity ++ "; la a6, bv_mtx_committed_chunk_overflow\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  bnez a1, .Lbv_mtx_bail                         # chunked table full -> conservative\n" ++
  "  la t4, bv_mtx_committed_chunk_count; sd a0, 0(t4)\n" ++
  blockVerdictMtxCoinbaseFeeEffect ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_loop\n" ++
  ".Lbv_mtx_done:\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_mtx_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_mtx_refund; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_mtx_calldata; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_count; la t5, bv_tx_count; ld t5, 0(t5); sd t5, 0(t4)\n" ++
  blockVerdictMtxValidationTail ++
  ".Lbv_mtx_creation_unsupported:\n" ++
  bvReceiptsShapeSet 60 false ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_dispatch_unsupported:\n" ++
  bvRuntimeCompletenessSet 4 ++ bvReceiptsShapeSet 61 false ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_bail:\n" ++
  bvRuntimeCompletenessSet 5 ++ bvReceiptsShapeSet 62 false ++  ".Lbv_mtx_bail_after_shape:\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"

end EvmAsm.Codegen
