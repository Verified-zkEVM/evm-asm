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
import EvmAsm.Codegen.Programs.BlockVerdictDepositFallback
import EvmAsm.Codegen.Programs.BlockVerdictCreationStage

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
  "  la t1, bv_deposit_capture_only; sd zero, 0(t1); la t1, bv_deposit_runtime_capture_complete; sd zero, 0(t1)\n" ++
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  jal ra, bal_txs_independent\n" ++
  "  beqz a0, .Lbv_mtx_independent_deposit_check\n" ++
  "  li t0, 1; bne a0, t0, .Lbv_mtx_bail            # parse error -> conservative\n" ++
  "  jal ra, block_verdict_all_direct_deposit_txs\n" ++
  "  bnez a0, .Lbv_mtx_deposit_capture_mark\n" ++
  -- bmvmx.5.5.10 whitelist v0: an interacting non-deposit block enters the full
  -- sequential lane only when every BAL account with storage_changes rows is
  -- whitelisted (the four request predeploys, EIP-2935/4788 modeled-system,
  -- EIP-6110 deposit contract). Block-end system writes live in
  -- bv_system_storage_log and per-tx user SSTOREs in bv_user_storage_log,
  -- both consulted by the storage/tuple comparators. Any other interaction
  -- shape keeps today's posture: conservative bail (fail-closed).
  "  la t0, bv_bal_start; ld a0, 0(t0); la t0, bv_bal_len; ld a1, 0(t0)\n" ++
  "  jal ra, bal_storage_whitelist_clean\n" ++
  -- The full multi-transaction runtime below materializes and receipt-checks
  -- this substrate-backed path; do not retain the former whitelist-v0 FR gate.
  "  j .Lbv_mtx_independence_ok\n" ++
  ".Lbv_mtx_independent_deposit_check:\n" ++
  "  jal ra, block_verdict_all_direct_deposit_txs\n" ++
  "  beqz a0, .Lbv_mtx_independence_ok              # ordinary independent lane\n" ++
  ".Lbv_mtx_deposit_capture_mark:\n" ++
  "  li t0, 1; la t1, bv_deposit_capture_only; sd t0, 0(t1)\n" ++
  ".Lbv_mtx_independence_ok:\n" ++
  -- Build the sorted sender index once from public keys. The exact per-tx nonce
  -- check below binary-searches this table and mutates the count field as the
  -- running block-global nonce delta (transactions plus valid EIP-7702
  -- authorizations); the B1 final-nonce tail consumes that same table.
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
  -- The historical S1 authority materialization below is retained only as a
  -- frozen reference for the old proof artifact.  It is not a valid live
  -- state source: it is block-final/header seeded and can reject before the
  -- ordered AccountState transaction pass runs.  The sole live parser and
  -- writer is `eip7702_auth_state_prepare` at the common transaction boundary.
  "  j .Lbv_mtx_state_init\n" ++
  -- S1: materialize the ordered authority state once at the multi-tx pass
  -- boundary.  The event stream starts with every transaction sender, then
  -- adds each successfully recovered type-4 authority.  It intentionally
  -- does not decide authorization validity here: S2 consumes this immutable
  -- header-seeded table and applies the ordered nonce/code predicate once,
  -- shared by every gas/result pass.
  "  la t0, bv_eip7702_authority_event_count; la t1, bv_tx_count; ld t1, 0(t1); sd t1, 0(t0); la t0, bv_eip7702_authority_overflow; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_eas_sender_copy_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_eas_sender_copy_done\n" ++
  "  slli t3, t1, 6; la t4, bv_mtx_skip_list; add t4, t4, t3; slli t3, t1, 5; la t5, nea_sort_b; add t5, t5, t3; li t6, 0\n" ++
  ".Lbv_eas_sender_copy_bytes:\n" ++
  "  li a0, 32; beq t6, a0, .Lbv_eas_sender_copy_next\n" ++
  "  add a0, t4, t6; lbu a1, 0(a0); add a0, t5, t6; sb a1, 0(a0); addi t6, t6, 1; j .Lbv_eas_sender_copy_bytes\n" ++
  ".Lbv_eas_sender_copy_next:\n" ++
  "  addi t1, t1, 1; la t0, bv_mtx_skip_idx; sd t1, 0(t0); j .Lbv_eas_sender_copy_loop\n" ++
  ".Lbv_eas_sender_copy_done:\n" ++
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_eas_tx_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_eas_materialize\n" ++
  "  la a0, bv_mtx_ctx; mv a1, t1; jal ra, multi_tx_nth_context; la t0, bv_mtx_ctx; ld t2, 0(t0); bnez t2, .Lbv_sender_nonce_fail\n" ++
  "  ld t2, 160(t0); li t3, 4; bne t2, t3, .Lbv_eas_tx_next\n" ++
  -- Field 9 is the type-4 authorization list.  A malformed list is a
  -- fail-closed verdict error; an unrecoverable signature simply contributes
  -- no authority event, matching the later validity admission semantics.
  "  ld a0, 176(t0); ld a1, 184(t0); li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; jal ra, rlp_list_nth_item; bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 176(t0); la t2, b1an_auth_off; ld t2, 0(t2); add t1, t1, t2; la t2, b1an_auth_len; ld a1, 0(t2); mv a0, t1; la a2, b1an_auth_count; jal ra, rlp_list_count_items; bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, b1an_auth_i; sd zero, 0(t0)\n" ++
  ".Lbv_eas_auth_loop:\n" ++
  "  la t0, b1an_auth_i; ld t3, 0(t0); la t0, b1an_auth_count; ld t6, 0(t0); bgeu t3, t6, .Lbv_eas_tx_next\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 176(t0); la t1, b1an_auth_off; ld t1, 0(t1); add a0, a0, t1; la t1, b1an_auth_len; ld a1, 0(t1); mv a2, t3; la a3, b1an_item_off; la a4, b1an_item_len; jal ra, rlp_item_span; bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 176(t0); la t1, b1an_auth_off; ld t1, 0(t1); add a0, a0, t1; la t0, b1an_item_off; ld t0, 0(t0); add a0, a0, t0; la t0, b1an_item_len; ld a1, 0(t0); la a2, b1an_authority; la a3, b1an_recover_scratch; jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Lbv_eas_auth_next\n" ++
  "  la t0, bv_eip7702_authority_event_count; ld t1, 0(t0); li t2, " ++ toString bvEip7702AuthorityEventCapacity ++ "; bgeu t1, t2, .Lbv_sender_nonce_fail; slli t2, t1, 5; la t5, nea_sort_b; add t5, t5, t2; la t4, b1an_authority; li t2, 0\n" ++
  ".Lbv_eas_auth_copy:\n" ++
  "  li t6, 32; beq t2, t6, .Lbv_eas_auth_append\n" ++
  "  add t6, t4, t2; lbu a0, 0(t6); add t6, t5, t2; sb a0, 0(t6); addi t2, t2, 1; j .Lbv_eas_auth_copy\n" ++
  ".Lbv_eas_auth_append:\n" ++
  "  addi t1, t1, 1; la t0, bv_eip7702_authority_event_count; sd t1, 0(t0)\n" ++
  ".Lbv_eas_auth_next:\n" ++
  "  la t0, b1an_auth_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_eas_auth_loop\n" ++
  ".Lbv_eas_tx_next:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_eas_tx_loop\n" ++
  ".Lbv_eas_materialize:\n" ++
  "  la a0, nea_sort_b; la t0, bv_eip7702_authority_event_count; ld a1, 0(t0); la a2, bv_eip7702_authority_table; li a3, " ++ toString bvEip7702AuthorityEventCapacity ++ "; la a4, bv_eip7702_authority_count; jal ra, eip7702_authority_state_materialize; bnez a0, .Lbv_sender_nonce_fail\n" ++
  ".Lbv_mtx_state_init:\n" ++
  "  la t0, bv_mtx_i; sd zero, 0(t0)\n" ++
  -- Execution CodeState is block-lived in the sequential lane.  The callable
  -- dispatcher resets only its pending overlay; durable state and retained
  -- comparator bytes survive until this loop finishes.
  -- CodeState is the sole execution code/existence model for every block,
  -- including the one-transaction case.  The immutable witness is consulted
  -- only after its pending and durable overlays miss.
  "  la t0, code_state_mtx_active; li t1, 1; sd t1, 0(t0); la t0, account_state_durable_count; sd zero, 0(t0); la t0, account_state_pending_count; sd zero, 0(t0); la t0, account_state_created_count; sd zero, 0(t0); la t0, account_state_delete_count; sd zero, 0(t0); la t0, account_state_overflow; sd zero, 0(t0)\n" ++
  "  la t0, exec_code_effect_count; sd zero, 0(t0); la t0, exec_code_effect_next; sd zero, 0(t0); la t0, exec_code_effect_overflow; sd zero, 0(t0)\n" ++
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
  -- The dispatcher resets this marker only when it is reached.  Every MTx
  -- iteration must begin phase-zero as well: a pre-dispatch rejection or an
  -- EOA/non-runtime route otherwise inherits a previous transaction's
  -- successful preparation and incorrectly retains staged authorization gas.
  "  la t0, runtime_tx_auth_phase_applied; sd zero, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; mv a1, t1; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_ctx; ld t2, 0(t0); bnez t2, .Lbv_mtx_bail\n" ++
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
  -- `multi_tx_nth_context` deliberately leaves ctx+24 (the signer public-key
  -- pointer) as a caller input.  The runtime dispatcher consumes that field to
  -- derive and stage top-level CALLER/ORIGIN, so retain this tx's already
  -- authenticated public_keys[i]+1 pointer before the nonce helper clobbers a0.
  "  la t0, bv_mtx_ctx; sd a0, 24(t0)\n" ++
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
  "  mv t6, a1; ld t5, 32(t6)\n" ++
  "  la t0, bv_mtx_nonce_pre; ld t0, 0(t0)\n" ++
  "  add t0, t0, t5\n" ++                                       -- t0 = expected = pre_nonce + count
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                      -- t1 = tx.nonce
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                   -- tx.nonce != pre+count -> reject (Nonce*Error)
  -- Commit this transaction's sender increment only after its nonce matched,
  -- then apply every valid authorization from the already-classified type-4
  -- payload.  This is the execution-specs order: process_transaction first,
  -- process_authorization_list second.
  "  addi t5, t5, 1; sd t5, 32(t6)\n" ++
  -- Sole EIP-7702 state/gas writer: run at the common per-transaction
  -- boundary, before recipient routing.  The old B1 replay is a frozen
  -- reference only; executing it here would be a second writer and can bail
  -- a later transaction before it observes AccountState's prior commit.
  -- Authorization recovery is part of the preparation phase itself.  The EOA
  -- shortcut installs this backend later, so the common boundary must stage it
  -- first or valid authorizations are silently skipped before their charges.
  "  la t0, ecrecover_backend_ptr; la t1, secp256k1_recover_pubkey_staged; sd t1, 0(t0)\n" ++
  -- One live intrinsic/auth accounting boundary.  It uses AccountState as of
  -- this transaction and writes the ordinary intrinsic-state settlement cell
  -- directly; no block-final BAL replay or auth overlay follows later.
  "  la t0, bv_mtx_ctx; ld a0, 8(t0); ld a1, 16(t0); ld a2, 176(t0); ld a3, 184(t0); la a4, bv_mtx_sender_addr; ld a5, 160(t0); la t0, bv_mtx_i; ld a6, 0(t0); jal ra, block_verdict_tx_state_gas_inline_prepare\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
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
  -- Creation needs the same sender/public-key and nonce setup as every other
  -- multi-tx item before its runtime adapter can derive CREATE(sender, nonce).
  -- Route here rather than at context extraction, where ctx+24 is deliberately
  -- still null and the generalized runner would hash a null sender pointer.
  "  la t0, bv_mtx_ctx; ld t1, 48(t0); bnez t1, .Lbv_mtx_creation\n" ++
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
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  "  la t0, bv_mtx_ctx; addi a0, t0, 72; ld a1, 80(s0); ld a2, 88(s0); li a3, 0\n" ++
  "  la t0, svf_codes_ptr; ld a4, 0(t0)\n" ++          -- evm-asm-uzb6b: resolver codes base (top level re-adds *svf_codes_ptr)
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
  -- fhsxz.2.4.2.57.11.6.5: gate the PRE-state header to THIS (mtx) dispatch call only.
  -- Single-tx dispatch (.Lbv_cd_* path, line ~717) leaves the flag 0 -> sv_this_rlp,
  -- byte-identical to #8686 (no >10% regression recurrence). Reset immediately after.
  "  li t0, 1; la t1, dtrc_use_pre_header; sd t0, 0(t1)\n" ++
  -- bmvmx.7.2: multi-tx contract-recipient top-level EIP-7708 value-transfer log.
  -- Stage before runtime dispatch and let dispatcher_reemit_pending_tl append it after
  -- the dispatcher resets per-tx event logs, preserving spec order: top-level value
  -- move first, then logs produced by recipient code.
  "  la t0, bv_mtx_ctx; addi t0, t0, 96; ld t1, 0(t0); ld t2, 8(t0); or t1, t1, t2; ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2\n" ++
  "  beqz t1, .Lbv_mtx_tl7708_skip\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_tl_selfcmp:\n" ++
  "  beqz t2, .Lbv_mtx_tl7708_skip\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_tl_notself\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_tl_selfcmp\n" ++
  ".Lbv_mtx_tl_notself:\n" ++
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
  "  li t1, 1; la t0, eip7708_tl_typed_avail; sd t1, 0(t0)\n" ++
  "  la t0, bv_pending_tl_flag; sd t1, 0(t0)\n" ++
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
  "  la t0, evm_env; ld t1, 448(t0); la t0, bv_tx_effect_snap_storage_count; sd t1, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; ld a1, 80(s0); ld a2, 88(s0); jal ra, dispatch_tx_runtime_code\n" ++
  "  la t0, create_nonce_table_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, exec_code_effect_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, account_state_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
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
  -- OOG/exceptional depth-0 exits do not pass through frame_return's REVERT
  -- truncation. Restore the persistent SSTORE log to the exact pre-dispatch
  -- count before publishing committed storage for the next transaction.
  "  la t0, bv_tx_effect_snap_storage_count; ld t1, 0(t0); la t0, evm_env; sd t1, 448(t0)\n" ++
  ".Lbv_mtx_effects_kept:\n" ++
  -- Contract/EOA contexts retain their raw recipient here; the creation route
  -- above has re-keyed ctx+72 to bv_create_addr before joining this postlude.
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 5; la t2, bv_mtx_effective_recipient_table; add t2, t2, t1; la t0, bv_mtx_ctx; addi t0, t0, 72; li t3, 20\n" ++
  ".Lbv_mtx_effective_recipient_copy:\n  beqz t3, .Lbv_mtx_effective_recipient_done; lbu t4, 0(t0); sb t4, 0(t2); addi t0, t0, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbv_mtx_effective_recipient_copy\n" ++
  ".Lbv_mtx_effective_recipient_done:\n" ++
  -- The sole MTx terminal state-gas finalizer.  Every supported terminal
  -- route (contract, creation, and EOA) reaches this postlude exactly once;
  -- a zero receipt status retains only intrinsic/auth state gas after a body
  -- rollback, while a successful status includes the captured execution part.
  "  la t0, bv_mtx_i; ld a0, 0(t0); slli t1, a0, 3; la t2, bv_tx_status_arr; add t2, t2, t1; ld a1, 0(t2); jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  -- bmvmx.5.5.10 PR-2: capture this tx's surviving SSTORE rows into the per-tx
  -- USER-write side arena (bv_user_storage_log) BEFORE the next dispatch's setup
  -- resets persistentLogLength. a4 = tx status; a failed tx commits nothing
  -- (mirrors state clearing), so capture only on success. The capture helper
  -- filters seed/preload rows through explicit per-row provenance rather than
  -- assuming they occupy a stable prefix of the live log.
  -- Overflow/malformed -> .Lbv_mtx_bail (fail-closed, today's posture).
  "  beqz a4, .Lbv_mtx_snapshot_empty\n" ++
  "  li a0, 0; la t0, evm_env; ld a1, 448(t0); li a2, 0xa0630000; la a3, bv_user_storage_log; la a4, bv_user_storage_txindex; la a5, bv_user_storage_log_count; la t0, bv_mtx_i; ld a6, 0(t0); addi a6, a6, 1; li a7, " ++ toString bvUserStorageLogCapacity ++ "\n" ++
  "  jal ra, capture_system_storage_exec_rows\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  -- Commit the exact unseeded slice just copied into the user-write arena.
  "  la t0, bv_system_storage_capture_old_count; ld t1, 0(t0); la t0, bv_system_storage_capture_new_count; ld a2, 0(t0); sub a2, a2, t1; slli t2, t1, 7; la a1, bv_user_storage_log; add a1, a1, t2; j .Lbv_mtx_snapshot_ready\n" ++
  ".Lbv_mtx_snapshot_empty:\n" ++
  "  la a1, bv_user_storage_log; li a2, 0\n" ++
  ".Lbv_mtx_snapshot_ready:\n" ++
  -- Commit the just-successful transaction's current CodeState overlay before
  -- the next callable dispatch.  A failed receipt commits no code/existence
  -- mutations, exactly like its effect-log rollback above.
  -- Match `process_message`'s two snapshots: a successful body commits all
  -- pending AccountState; a failed body still commits the authorization phase
  -- iff the dispatcher reached the post-preparation coverage point.  A
  -- preparation OOG never reaches that point and therefore drops pending auth.
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 3; la t2, bv_tx_status_arr; add t2, t2, t1; ld t2, 0(t2); bnez t2, .Lbv_mtx_code_commit; la t0, runtime_tx_auth_phase_applied; ld t2, 0(t0); bnez t2, .Lbv_mtx_code_commit\n" ++
  "  la t0, account_state_pending_count; sd zero, 0(t0); la t0, account_state_created_count; sd zero, 0(t0); la t0, account_state_delete_count; sd zero, 0(t0); j .Lbv_mtx_code_commit_done\n" ++
  ".Lbv_mtx_code_commit:\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 176(t0); ld a1, 184(t0); la a2, bv_mtx_sender_addr; ld a3, 160(t0); li a4, 1; jal ra, eip7702_auth_state_prepare; bnez a0, .Lbv_mtx_bail\n" ++
  "  jal ra, account_state_commit_pending; bnez a0, .Lbv_mtx_bail\n" ++
  -- `account_state_commit_pending` uses a1/a2 for durable-map operations.
  -- Reconstruct the successful transaction's captured storage slice before the
  -- committed-storage upsert: a1/a2 are caller-saved and must not be reused
  -- across that call.  This is the same slice computed at snapshot_ready.
  "  la t0, bv_system_storage_capture_old_count; ld t1, 0(t0); la t0, bv_system_storage_capture_new_count; ld a2, 0(t0); sub a2, a2, t1; slli t2, t1, 7; la a1, bv_user_storage_log; add a1, a1, t2\n" ++
  ".Lbv_mtx_code_commit_done:\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow; ld t1, 0(t0); bnez t1, .Lbv_mtx_bail\n" ++
  "  la a0, evm_selfdestruct_destroyed_table; la t0, evm_selfdestruct_destroyed_count; ld a7, 0(t0)\n" ++
  "  la a3, bv_mtx_committed_chunked; la t0, bv_mtx_committed_chunk_count; ld a4, 0(t0)\n" ++
  "  li a5, " ++ toString bvMtxCommittedChunkCapacity ++ "; la a6, bv_mtx_committed_chunk_overflow\n" ++
  "  jal ra, bv_mtx_committed_chunked_snapshot_upsert\n" ++
  "  bnez a1, .Lbv_mtx_bail                         # chunked table full -> conservative\n" ++
  "  la t4, bv_mtx_committed_chunk_count; sd a0, 0(t4)\n" ++
  blockVerdictMtxCoinbaseFeeEffect ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_loop\n" ++
  ".Lbv_mtx_done:\n" ++
  "  la t0, bv_deposit_capture_only; ld t0, 0(t0); beqz t0, .Lbv_mtx_publish\n" ++
  "  li t0, 1; la t1, bv_deposit_runtime_capture_complete; sd t0, 0(t1)\n" ++
  -- The deposit capture-only lane has complete per-tx runtime arrays. Publish
  -- them to the common exact-gas/EIP-7778 and receipt gates just like the
  -- ordinary multi-transaction lane.
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_mtx_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_mtx_refund; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_mtx_calldata; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_count; la t5, bv_tx_count; ld t5, 0(t5); sd t5, 0(t4)\n" ++
  bvRuntimeCompletenessSet 5 ++ bvReceiptsShapeSet 62 true ++
  "  j .Lbv_after_tx_gas_precharge\n" ++
  ".Lbv_mtx_publish:\n" ++
  "  la t4, bvgr_runtime_gas_left_ptr; la t5, bv_mtx_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_refund_counter_ptr; la t5, bv_mtx_refund; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_calldata_floor_ptr; la t5, bv_mtx_calldata; sd t5, 0(t4)\n" ++
  "  la t4, bvgr_runtime_count; la t5, bv_tx_count; ld t5, 0(t5); sd t5, 0(t4)\n" ++
  blockVerdictMtxValidationTail ++
  ".Lbv_mtx_creation:\n" ++
  -- The generalized creation runner is shared with the single-tx route.  Its
  -- caller contract needs a real CREATE frame first: sender/public-key and
  -- nonce have already been established by the common mtx prelude above.
  "  la t0, bv_mtx_ctx; la t1, bv_mtx_base_fee_be; sd t1, 32(t0)\n" ++
  "  la a0, bv_mtx_sender_addr; la t0, sttc_nonce; ld a1, 0(t0); la a2, bv_create_addr; jal ra, address_compute_create\n" ++
  -- EIP-684 observes the current block state before the immutable witness.
  -- A durable CodeState entry is a prior-tx live account and collides; a
  -- durable tombstone is a same-tx-created account already deleted at an
  -- earlier transaction boundary, so it deliberately falls through to the
  -- pre-block predicate (where it is absent and may be recreated).
  "  la a0, bv_create_addr; jal ra, code_state_lookup_current\n" ++
  "  beqz a0, .Lbv_mtx_creation_header_collision\n" ++
  "  li t0, 3; beq a0, t0, .Lbv_mtx_creation_header_collision\n" ++
  "  j .Lbv_mtx_creation_unsupported\n" ++
  ".Lbv_mtx_creation_header_collision:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_create_addr; ld a3, 80(s0); ld a4, 88(s0); jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_creation_unsupported\n" ++
  "  la t0, hcon_predicate; ld t0, 0(t0); bnez t0, .Lbv_mtx_creation_unsupported\n" ++
  -- Fresh target: mirror the single CREATE prepare_dispatch charge.  A
  -- collision stays conservative until its error-receipt publication is also
  -- indexed; never run initcode for a target whose EIP-684 predicate is true.
  "  la t0, runtime_tx_create_state_charge; sd zero, 0(t0)\n" ++
  "  la t0, hcon_acct_struct; ld t1, 8(t0); ld t2, 16(t0); or t1, t1, t2; ld t2, 24(t0); or t1, t1, t2; ld t2, 32(t0); or t1, t1, t2; bnez t1, .Lbv_mtx_creation_charge_ready\n" ++
  liAmsterdamNewAccountStateGas "t1" ++
  "  la t0, runtime_tx_create_state_charge; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_creation_charge_ready:\n" ++
  -- A creation transaction cannot be EIP-7702.  Its access-list state is
  -- still part of intrinsic gas, so initialize the same runtime controls as
  -- the single creation route; nonzero parse failures stay fail-closed.
  "  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0); la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_access_list_ptr; sd zero, 0(t0); la t0, runtime_tx_access_list_len; sd zero, 0(t0); la t0, runtime_tx_access_list_seed_fn; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_list_ptr; sd zero, 0(t0); la t0, runtime_tx_auth_list_len; sd zero, 0(t0); la t0, runtime_tx_auth_warm_fn; sd zero, 0(t0); la t0, runtime_tx_auth_count; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0); la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0); la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_ctx; ld t0, 160(t0); beqz t0, .Lbv_mtx_creation_access_done\n" ++
  "  li a2, 7; li t1, 1; beq t0, t1, .Lbv_mtx_creation_access_field; li a2, 8; li t1, 2; beq t0, t1, .Lbv_mtx_creation_access_field; li t1, 3; beq t0, t1, .Lbv_mtx_creation_access_field; j .Lbv_mtx_creation_unsupported\n" ++
  ".Lbv_mtx_creation_access_field:\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 176(t0); ld a1, 184(t0); la a3, bsg_access_off; la a4, bsg_access_len; jal ra, rlp_list_nth_item; bnez a0, .Lbv_mtx_creation_unsupported\n" ++
  "  la t0, bv_mtx_ctx; ld t0, 176(t0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1; la t1, bsg_access_len; ld a1, 0(t1); la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count; jal ra, access_list_count; bnez a0, .Lbv_mtx_creation_unsupported\n" ++
  "  la t0, bv_mtx_ctx; ld t0, 176(t0); la t1, bsg_access_off; ld t1, 0(t1); add t2, t0, t1; la t0, runtime_tx_access_list_ptr; sd t2, 0(t0); la t1, bsg_access_len; ld t2, 0(t1); la t0, runtime_tx_access_list_len; sd t2, 0(t0); la t0, runtime_tx_access_list_seed_fn; la t1, seed_tx_access_list; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_creation_access_done:\n" ++
  -- Match the normal mtx dispatch transaction boundary: effects and storage
  -- begin with a rollback checkpoint, and the dispatcher sees the block-pre
  -- header while resolving nested accounts.
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0); li t0, 1; la t1, dtrc_use_pre_header; sd t0, 0(t1)\n" ++
  "  la t0, exec_nonstorage_effect_count; ld t1, 0(t0); la t0, bv_tx_effect_snap_ns_count; sd t1, 0(t0); la t0, exec_nonstorage_effect_overflow; ld t1, 0(t0); la t0, bv_tx_effect_snap_ns_overflow; sd t1, 0(t0)\n" ++
  "  la t0, exec_code_effect_count; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_count; sd t1, 0(t0); la t0, exec_code_effect_next; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_next; sd t1, 0(t0); la t0, exec_code_effect_overflow; ld t1, 0(t0); la t0, bv_tx_effect_snap_code_overflow; sd t1, 0(t0)\n" ++
  "  la t0, evm_env; ld t1, 448(t0); la t0, bv_tx_effect_snap_storage_count; sd t1, 0(t0)\n" ++
  "  la t0, bv_creation_output_mode; li t1, 1; sd t1, 0(t0); la t0, bv_mtx_i; ld t1, 0(t0); la t0, bv_creation_output_index; sd t1, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; la t0, bv_exec_p; ld a1, 0(t0); jal ra, block_verdict_single_tx_creation_runtime\n" ++
  "  la t0, bv_creation_output_mode; sd zero, 0(t0); la t0, dtrc_use_pre_header; sd zero, 0(t0)\n" ++
  "  bnez a0, .Lbv_mtx_creation_unsupported\n" ++
  -- Re-key the shared mtx postlude to the created account.  The context is
  -- replaced on the next loop iteration, and only its address slot is read by
  -- the postlude's committed-storage snapshot.
  "  la t0, bv_create_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_creation_key_copy:\n  beqz t2, .Lbv_mtx_creation_post; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_creation_key_copy\n" ++
  ".Lbv_mtx_creation_post:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t0, t1, 3; la t3, bv_tx_status_arr; add t3, t3, t0; ld a4, 0(t3)\n" ++
  "  bnez a4, .Lbv_mtx_effects_kept\n" ++
  "  la t0, bv_tx_effect_snap_ns_count; ld t1, 0(t0); la t0, exec_nonstorage_effect_count; sd t1, 0(t0); la t0, bv_tx_effect_snap_ns_overflow; ld t1, 0(t0); la t0, exec_nonstorage_effect_overflow; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_code_count; ld t1, 0(t0); la t0, exec_code_effect_count; sd t1, 0(t0); la t0, bv_tx_effect_snap_code_next; ld t1, 0(t0); la t0, exec_code_effect_next; sd t1, 0(t0); la t0, bv_tx_effect_snap_code_overflow; ld t1, 0(t0); la t0, exec_code_effect_overflow; sd t1, 0(t0)\n" ++
  "  la t0, bv_tx_effect_snap_storage_count; ld t1, 0(t0); la t0, evm_env; sd t1, 448(t0); j .Lbv_mtx_effects_kept\n" ++
  ".Lbv_mtx_creation_unsupported:\n" ++
  -- A creation transaction is not yet dispatched by this loop, but every
  -- preceding transaction has an exact settled runtime result in the strided
  -- arrays.  Do not discard that information: execution-specs checks the next
  -- transaction's declared regular reservation against the regular gas already
  -- consumed by the settled prefix.  This catches an invalid transaction after
  -- an otherwise supported prefix without guessing the creation transaction's
  -- execution result.  Any parse/result failure remains the conservative bail.
  "  la t0, bv_mtx_i; ld a5, 0(t0); beqz a5, .Lbv_mtx_creation_prefix_done\n" ++
  "  la t0, bv_exec_p; ld a0, 0(t0); la a1, bvgr_tx_gas_limits; li a2, " ++ toString bvMtxFullTxCap ++ "; jal ra, block_verdict_tx_gas_limits\n" ++
  "  bnez a0, .Lbv_mtx_creation_prefix_done\n" ++
  "  la t0, bv_exec_p; ld t0, 0(t0); addi a0, t0, 412; jal ra, bgv_u64le\n" ++
  "  la a1, bvgr_tx_gas_limits; la a2, bv_mtx_gas_left; la a3, bv_mtx_refund; la a4, bv_mtx_calldata\n" ++
  "  la t0, bv_mtx_i; ld a5, 0(t0); la a6, bvgr_block_gas_increments; li a7, 0\n" ++
  "  jal ra, eip7778_remaining_block_gas_from_results\n" ++
  "  bnez a0, .Lbv_mtx_creation_prefix_done\n" ++
  "  la t0, bv_mtx_creation_prefix_used; sd a2, 0(t0)\n" ++
  "  la t1, bv_exec_p; ld t1, 0(t1); addi a0, t1, 412; jal ra, bgv_u64le\n" ++
  "  la t0, bv_mtx_creation_prefix_used; ld t0, 0(t0)\n" ++
  "  bltu a0, t0, .Lbv_eip8037_gas_fail\n" ++
  "  sub t1, a0, t0; la t0, bv_mtx_ctx; ld t2, 40(t0); li t3, 16777216; bleu t2, t3, .Lbv_mtx_creation_cap_done; mv t2, t3\n" ++
  ".Lbv_mtx_creation_cap_done:\n" ++
  "  bgtu t2, t1, .Lbv_eip8037_gas_fail\n" ++
  ".Lbv_mtx_creation_prefix_done:\n" ++
  -- The receipt root is consensus-critical even when this runtime lane cannot
  -- yet materialize every result.  Enforce it so an unsupported multi-tx shape
  -- cannot silently accept a doctored header; incomplete materialization now
  -- fails closed and is an explicit make-exact follow-up.
  bvReceiptsShapeSet 60 true ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_dispatch_unsupported:\n" ++
  bvRuntimeCompletenessSet 4 ++ bvReceiptsShapeSet 61 true ++
  "  j .Lbv_mtx_bail_after_shape\n" ++
  ".Lbv_mtx_bail:\n" ++
  bvRuntimeCompletenessSet 5 ++ bvReceiptsShapeSet 62 true ++  ".Lbv_mtx_bail_after_shape:\n" ++
  "  j .Lbv_after_tx_gas_precharge\n"

/-- Rebuild S1 immediately before the gas replay from authenticated immutable
    transaction data. `nea_sort_a` is only the immediate input to the radix
    materializer; no later phase treats it as durable state. -/
def blockVerdictEip7702AuthorityReplayMaterializeFunction : String :=
  "block_verdict_eip7702_authority_replay_materialize:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  la t0, bv_tx_count; ld s1, 0(t0); li t1, " ++ toString bvMtxFullTxCap ++ "; bgtu s1, t1, .Leasr_fail\n" ++
  "  la s2, nea_sort_a; li s0, 0\n" ++
  ".Leasr_sender_loop:\n" ++
  "  bgeu s0, s1, .Leasr_sender_done\n" ++
  "  slli t0, s0, 6; add t0, t0, s0; la t1, bv_public_keys_ptr; ld t1, 0(t1); addi a0, t1, 1; add a0, a0, t0\n" ++
  "  slli t0, s0, 5; add a1, s2, t0; jal ra, address_from_pubkey\n" ++
  "  addi s0, s0, 1; j .Leasr_sender_loop\n" ++
  ".Leasr_sender_done:\n" ++
  "  la t0, bv_eip7702_authority_event_count; sd s1, 0(t0); la t0, bv_eip7702_authority_overflow; sd zero, 0(t0)\n" ++
  "  li s0, 0\n" ++
  ".Leasr_tx_loop:\n" ++
  "  bgeu s0, s1, .Leasr_materialize\n" ++
  "  la a0, bv_mtx_ctx; mv a1, s0; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 0(t0); bnez t1, .Leasr_fail\n" ++
  "  ld t1, 160(t0); li t2, 4; bne t1, t2, .Leasr_tx_next\n" ++
  "  ld t1, 176(t0); ld t2, 184(t0); li a2, 9; la a3, b1an_auth_off; la a4, b1an_auth_len; mv a0, t1; mv a1, t2; jal ra, rlp_list_nth_item; bnez a0, .Leasr_fail\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 176(t0); la t2, b1an_auth_off; ld t2, 0(t2); add a0, t1, t2; la t2, b1an_auth_len; ld a1, 0(t2); la a2, b1an_auth_count; jal ra, rlp_list_count_items; bnez a0, .Leasr_fail\n" ++
  "  li s3, 0\n" ++
  ".Leasr_auth_loop:\n" ++
  "  la t0, b1an_auth_count; ld t1, 0(t0); bgeu s3, t1, .Leasr_tx_next\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 176(t0); la t2, b1an_auth_off; ld t2, 0(t2); add a0, t1, t2; la t2, b1an_auth_len; ld a1, 0(t2); mv a2, s3; la a3, b1an_item_off; la a4, b1an_item_len; jal ra, rlp_item_span; bnez a0, .Leasr_fail\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 176(t0); la t2, b1an_auth_off; ld t2, 0(t2); add a0, t1, t2; la t0, b1an_item_off; ld t0, 0(t0); add a0, a0, t0; la t0, b1an_item_len; ld a1, 0(t0); la a2, b1an_authority; la a3, b1an_recover_scratch; jal ra, eip7702_authorization_recover_address\n" ++
  "  bnez a0, .Leasr_auth_next\n" ++
  "  la t0, bv_eip7702_authority_event_count; ld t1, 0(t0); li t2, " ++ toString bvEip7702AuthorityEventCapacity ++ "; bgeu t1, t2, .Leasr_fail; slli t2, t1, 5; add t2, s2, t2; la t3, b1an_authority; li t4, 0\n" ++
  ".Leasr_auth_copy:\n" ++
  "  li t5, 32; beq t4, t5, .Leasr_auth_append; add t5, t3, t4; lbu t6, 0(t5); add t5, t2, t4; sb t6, 0(t5); addi t4, t4, 1; j .Leasr_auth_copy\n" ++
  ".Leasr_auth_append:\n" ++
  "  addi t1, t1, 1; la t0, bv_eip7702_authority_event_count; sd t1, 0(t0)\n" ++
  ".Leasr_auth_next:\n" ++
  "  addi s3, s3, 1; j .Leasr_auth_loop\n" ++
  ".Leasr_tx_next:\n" ++
  "  addi s0, s0, 1; j .Leasr_tx_loop\n" ++
  ".Leasr_materialize:\n" ++
  "  la a0, nea_sort_a; la t0, bv_eip7702_authority_event_count; ld a1, 0(t0); la a2, bv_eip7702_authority_table; li a3, " ++ toString bvEip7702AuthorityEventCapacity ++ "; la a4, bv_eip7702_authority_count; jal ra, eip7702_authority_state_materialize; bnez a0, .Leasr_fail\n" ++
  "  li a0, 0; j .Leasr_ret\n" ++
  ".Leasr_fail:\n" ++
  "  li a0, 1\n" ++
  ".Leasr_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 64; ret\n"

end EvmAsm.Codegen
