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
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

/-- Stage the execution-start sender debit into the existing one-shot tuple.
    The tuple is consumed by `dispatcher_seed_pending_upfront_sender_balance`; it is
    deliberately not a B2.3 reconstruction.  `account_state_latest_balance`
    supplies the prior transaction's durable balance when present, otherwise
    the already-authenticated header lookup supplies the first transaction's
    balance. -/
private def blockVerdictMtxStageSenderUpfront : String :=
  -- The main fee gate intentionally preserves its existing handling for
  -- non-priceable malformed inputs.  Do not turn a diagnostic tuple into a
  -- second reject path: mirror the single-tx producer and stage only when a
  -- fresh effective-price calculation succeeds.
  "  la t0, bv_mtx_ctx; ld a0, 8(t0); ld a1, 16(t0); la a2, bv_mtx_base_fee_be; la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch; jal ra, tx_effective_gas_pricing\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; jal ra, account_state_latest_balance\n" ++
  "  bnez a0, .Lbv_mtx_su_have_pre\n" ++
  "  la t0, bv_mtx_sender_acct; addi t0, t0, 8; la t1, bv_pending_upfront_sender_pre; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  ".Lbv_mtx_su_have_pre:\n" ++
  -- `check_transaction` debits gas_limit * effective_gas_price, rather than
  -- the max-fee affordability reservation used immediately above.
  "  la a0, bv_fee_egp_scratch; la t0, bv_mtx_ctx; ld a1, 40(t0); la a2, bv_upfront_cost; jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  -- GH #10892: NO `tx.value` TERM IN THE STAGED DEBIT.  `process_transaction`
  -- debits `effective_gas_fee + blob_gas_fee` and NOTHING ELSE
  -- (`fork.py:1105-1108`); `check_transaction` adds `tx.value` AT THE COMPARISON
  -- (`:666`) and never stores it.  The value is moved by `process_message_call`,
  -- where a FAILED transfer reverts it -- so a pre-execution debit that includes it
  -- leaves the sender's recorded balance low by exactly `tx.value` on every block
  -- whose transfer did not take effect.  Measured 10/10 with the shortfall equal to
  -- the transaction value, spanning 2 wei to 32 ETH.
  --
  -- THE SUFFICIENCY CHECK IS UNAFFECTED: it builds its OWN `bv_upfront_cost` at
  -- `:320-355`, including its own `tx.value` add (annotated there), and that
  -- construction is untouched.  This one feeds only the staging subtract below.
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la t0, bv_upfront_blob_cost; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 160(t0); li t2, 3; bne t1, t2, .Lbv_mtx_su_blob_done\n" ++
  "  ld a0, 176(t0); ld a1, 184(t0); la a2, tcbg_struct; jal ra, tx_eip4844_decode\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la t0, tcbg_struct; lwu t1, 168(t0); lwu t2, 172(t0); la t3, bv_mtx_ctx; ld t3, 176(t3); add a0, t3, t1; mv a1, t2; la a2, bv_upfront_blob_count; jal ra, rlp_list_count_items\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la t0, bv_upfront_blob_count; ld a1, 0(t0); beqz a1, .Lbv_mtx_su_done; li t2, 6; bgtu a1, t2, .Lbv_mtx_su_done; slli a1, a1, 17\n" ++
  "  la a0, bsg_blob_price_be; la a2, bv_upfront_blob_cost; jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la a0, bv_upfront_cost; la a1, bv_upfront_blob_cost; la a2, bv_upfront_cost; jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  ".Lbv_mtx_su_blob_done:\n" ++
  "  la a0, bv_pending_upfront_sender_pre; la a1, bv_upfront_cost; la a2, bv_pending_upfront_sender_post; jal ra, u256_sub_be\n" ++
  "  bnez a0, .Lbv_mtx_su_done\n" ++
  "  la t0, bv_mtx_sender_addr; la t1, bv_pending_upfront_sender_addr; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); sd zero, 24(t1)\n" ++
  "  la t0, sttc_nonce; ld t1, 0(t0); addi t1, t1, 1; la t0, bv_pending_upfront_sender_nonce; sd t1, 0(t0)\n" ++
  "  li t1, 1; la t0, bv_pending_upfront_balance_flag; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_su_done:\n"

/-- Record the post-execution sender refund.  The preceding execution-start
    record has already placed the gas-limit debit in AccountState; this second
    record applies `create_ether(sender, gas_refund_amount)` from the actual
    dispatch result.  The transaction map upsert deliberately collapses both
    writes to the final per-transaction balance. -/
private def blockVerdictMtxRecordSenderRefund : String :=
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 3\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 40(t0); la t2, bv_mtx_gas_left; add t2, t2, t1; ld a1, 0(t2); la t2, bv_mtx_refund; add t2, t2, t1; ld a2, 0(t2); la t2, bv_mtx_calldata; add t2, t2, t1; ld a3, 0(t2); jal ra, tx_gas_result_increments\n" ++
  "  bnez a0, .Lbv_mtx_sr_done\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 40(t0); bgtu a2, t1, .Lbv_mtx_bail; sub a1, t1, a2\n" ++
  "  la a0, bv_fee_egp_scratch; la a2, bv_pending_upfront_sender_post; jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; jal ra, account_state_latest_balance\n" ++
  "  bnez a0, .Lbv_mtx_sr_have_pre\n" ++
  "  la t0, bv_mtx_sender_acct; addi t0, t0, 8; la t1, bv_pending_upfront_sender_pre; ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1); ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)\n" ++
  ".Lbv_mtx_sr_have_pre:\n" ++
  "  la a0, bv_pending_upfront_sender_pre; la a1, bv_pending_upfront_sender_post; la a2, bv_pending_upfront_sender_post; jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la t0, sttc_nonce; ld a3, 0(t0); addi a4, a3, 1; la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; la a2, bv_pending_upfront_sender_post; jal ra, record_nonstorage_effect\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  ".Lbv_mtx_sr_done:\n"

/-- Gated multi-transaction runtime-gas loop fragment.  Every block falls
    through to the MTx loop, which iterates zero times on an empty block;
    the former `bv_tx_count == 0` branch to `.Lbv_recipient_nc_done` and the
    `.Lbv_singletx` hop before it were duplicate tests of the same condition,
    both now removed. -/
def blockVerdictMtxRuntimeLoop : String :=
  -- evm-asm-fhsxz.2.4.2.57.11.6.2.2.2: gated multi-transaction runtime gas loop.
  -- Every non-empty block enters MTx. For 1..16 transactions, only when the block
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
  -- Production MTx selector: every block enters MTx, including the empty
  -- block; the loop iterates zero times there (matches execution-specs
  -- fork.py:913-914, which has no empty-block special case).  The former
  -- `bv_tx_count == 0` early branch to `.Lbv_recipient_nc_done` (an early
  -- exit, not a separate implementation) is removed.
  -- r59nm cleanup: retargeted from `.Lbv_singletx`, which re-tested this same
  -- unchanged `bv_tx_count` and so always fell through to here.  The label and
  -- its duplicate test are gone; this is the one-hop form of the path that was
  -- always taken.
  --
  -- Three facts that outlive the removed entry, recorded because they are not
  -- recoverable from what remains:
  --  * `i3djw_skip_list` is still BUILT (BlockVerdictFunction, the recipient +
  --    six modeled-system addresses) and never CONSULTED -- the list the live
  --    path passes is `bv_mtx_skip_list`, at the `BlockVerdictMtxTail` call to
  --    `bal_all_accounts_storage_consistent_skip_list`.  Measured: the
  --    single-tx all-accounts call site is reached on 0 of 60 EIP-7928
  --    fixtures, the MtxTail one on 56 of 60.
  --  * the single-tx region's INTERIOR is NOT dead: the MTX precompile lane
  --    jumps into it at `.Lbv_tx_gas_precharge_pc0_prefix` and from there
  --    reaches the whole precompile recipient family (ecrecover .. ecpairing).
  --    A forward closure from that entry reaches 141 of the 179 interior
  --    labels, so the extent must not be deleted as a block.
  --  * the 38 labels that closure does NOT reach are the recipient-exactness
  --    check and the skip-list construction.  Their removal is deferred to
  --    GH #10680, which retires the matching apparatus they belong to.
  -- #10591 routing: every block (including zero-tx) goes through the MTx
  -- loop; the loop iterates zero times on an empty block (matches
  -- execution-specs fork.py:913-914, which has no empty-block special case).
  "  la t0, bv_tx_count; ld t0, 0(t0)\n" ++
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
  -- Build the sorted distinct-sender index once from public keys.  B1 retains
  -- this address enumeration for its final BAL coverage check, but AccountState
  -- is the sole live nonce state: no execution path reads or mutates the row's
  -- count word.
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
  -- Execution CodeState is block-lived in the sequential lane. The callable
  -- dispatcher resets transaction-local pending overlays, including
  -- `account_state_pending_count`; it does not preserve that AccountState
  -- journal across dispatches. This reset is the live durability boundary in
  -- GH #10876: sender effects needed after dispatch must be materialized in
  -- durable state rather than left in the pending journal. Durable state and
  -- retained comparator bytes survive until this loop finishes.
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
  "  la t0, runtime_tx_post_preparation_reached; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_recipient_lookup_deferred; sd zero, 0(t0)\n" ++
  -- The tuple is one-shot.  A pre-dispatch terminal route must not leak an
  -- unconsumed predecessor tuple into this transaction.
  "  la t0, bv_pending_upfront_balance_flag; sd zero, 0(t0)\n" ++
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
  -- Exact sequential sender nonce check.  The first transaction falls back to
  -- the authenticated header account; later transactions read the durable
  -- sender snapshot published at their predecessors' inclusion boundary.
  -- sttc_nonce holds THIS tx's nonce (multi_tx_nth_context wrote it via tx_extract_nonce_and_gas).
  -- sender = address_from_pubkey(public_keys[i]+1): public_keys[i] = bv_public_keys_ptr + i*65
  -- (65-byte SEC1 0x04||x||y, verified bound to tx[i]'s signer by verify_public_keys_match_senders).
  -- i*65 = (i<<6)+i. account_at_header_state_root(pre-state) -> sender acct, nonce@0. s0+8/16/80/88
  -- are the same lookup args the legacy sender lookup uses (@128). Lookup
  -- fail/absent remains conservative, as before.
  "  la t0, bv_mtx_i; ld t1, 0(t0)\n" ++
  "  slli t2, t1, 6; add t1, t2, t1\n" ++                       -- t1 = i*65
  "  la t0, bv_public_keys_ptr; ld t0, 0(t0); add t0, t0, t1; addi a0, t0, 1\n" ++  -- a0 = public_keys[i]+1 (skip 0x04)
  -- `multi_tx_nth_context` deliberately leaves ctx+24 (the signer public-key
  -- pointer) as a caller input.  The runtime dispatcher consumes that field to
  -- derive and stage top-level CALLER/ORIGIN, so retain this tx's already
  -- authenticated public_keys[i]+1 pointer before the nonce helper clobbers a0.
  "  la t0, bv_mtx_ctx; sd a0, 24(t0)\n" ++
  "  la a1, bv_mtx_sender_addr; jal ra, address_from_pubkey\n" ++
  "  la a0, bv_mtx_sender_addr; la a1, bv_mtx_sender_acct; jal ra, account_state_latest_nonce\n" ++
  "  bnez a0, .Lbv_mtx_sender_nonce_current\n" ++
  ".Lbv_mtx_sender_header:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_sender_addr; li a3, 20; ld a4, 80(s0); ld a5, 88(s0); la a6, bv_mtx_sender_acct\n" ++
  "  jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_nonce_done\n" ++                         -- sender lookup failed/absent -> skip
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0); j .Lbv_mtx_sender_nonce_have\n" ++
  ".Lbv_mtx_sender_nonce_current:\n" ++
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0)\n" ++
  ".Lbv_mtx_sender_nonce_have:\n" ++
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                      -- t1 = tx.nonce
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                   -- tx.nonce != current sender nonce
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
  "  la t0, bv_upfront_blob_cost; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)\n" ++
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
  -- `process_transaction` increments the sender nonce before preparation.
  -- Publish that monotone execution fact both to the durable execution overlay
  -- and to the transaction-local BAL map. This is deliberately before the
  -- body rollback checkpoint: a failed body keeps the transaction nonce, while
  -- the checkpoint removes later body writes. Balance has later value, refund,
  -- and coinbase-credit writes, so it needs its own complete state transition
  -- rather than an inclusion-time snapshot here.
  "  la t0, sttc_nonce; ld a1, 0(t0); addi a1, a1, 1; la a0, bv_mtx_sender_addr; jal ra, account_state_publish_sender_inclusion; bnez a0, .Lbv_sender_nonce_fail\n" ++
  "  la t0, sttc_nonce; ld a2, 0(t0); addi a2, a2, 1; la a0, bv_mtx_sender_addr; li a1, 0; li a3, 0; li a4, 0; li a5, 0; li a6, " ++ toString accountWriteHasNonce ++ "; jal ra, account_write_record\n" ++
  blockVerdictMtxStageSenderUpfront ++
  -- Authorization preparation starts after sender inclusion and the upfront
  -- debit.  A preparation ExceptionalHalt must restore only auth-produced map
  -- rows; a later body revert restores the separate pre-dispatch mark instead
  -- and therefore retains the successful authorization phase.
  "  la t0, account_writes_undo_count; ld t1, 0(t0); la t0, account_writes_auth_prepare_mark; sd t1, 0(t0)\n" ++
  -- Sole EIP-7702 state/gas writer: run after the inclusion snapshot, before
  -- recipient routing.  The old B1 replay is a frozen reference only.
  "  la t0, ecrecover_backend_ptr; la t1, secp256k1_recover_pubkey_staged; sd t1, 0(t0)\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 8(t0); ld a1, 16(t0); ld a2, 176(t0); ld a3, 184(t0); la a4, bv_mtx_sender_addr; ld a5, 160(t0); la t0, bv_mtx_i; ld a6, 0(t0); jal ra, block_verdict_tx_state_gas_inline_prepare\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++
  ".Lbv_mtx_nonce_done:\n" ++
  -- Creation needs the same sender/public-key and nonce setup as every other
  -- multi-tx item before its runtime adapter can derive CREATE(sender, nonce).
  -- Route here rather than at context extraction, where ctx+24 is deliberately
  -- still null and the generalized runner would hash a null sender pointer.
  "  la t0, bv_mtx_ctx; ld t1, 48(t0); bnez t1, .Lbv_mtx_creation\n" ++
  -- The recipient classifier must see the accumulating execution state before
  -- it asks the immutable parent witness.  A successful tx1 CREATE publishes
  -- its code to AccountState, so tx2 must enter the contract lane even though
  -- the target is absent from the pre-block header.  This mirrors the layered
  -- resolver already used by child CALL-family handlers and by the dispatcher
  -- itself; only a genuine overlay miss may fall through to the header lookup.
  "  la a0, bv_mtx_ctx; addi a0, a0, 72; jal ra, account_state_lookup_current\n" ++
  "  li t1, 1; beq a0, t1, .Lbv_mtx_is_contract; bnez a0, .Lbv_mtx_is_contract\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_mtx_ctx; addi a2, a2, 72; ld a3, 80(s0); ld a4, 88(s0); la a5, bv_tx_recipient_code_hash\n" ++
  "  jal ra, code_hash_at_header_state_root\n" ++
  -- A status-2 recipient lookup stays a hard failure after preparation.  It is
  -- routed only through the shared EIP-7702 preparation prefix first: an
  -- ExceptionalHalt there restores the auth snapshot before the spec reads
  -- recipient code, while a completed prefix returns to the same status-2
  -- failure without executing a body.
  "  li t1, 2; bne a0, t1, .Lbv_mtx_recipient_lookup_resolved\n" ++
  "  la t0, bv_mtx_recipient_lookup_deferred; li t1, 1; sd t1, 0(t0); j .Lbv_mtx_is_contract\n" ++
  ".Lbv_mtx_recipient_lookup_resolved:\n" ++
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
  blockVerdictMtxPrecompileSettlement ++
  -- An inactive precompile is ordinary zero-byte code.  Rejoin the one
  -- top-level message processor instead of falling through to a second EOA
  -- settlement route.
  ".Lbv_mtx_precompile_not_active:\n" ++
  "  la t0, bv_mtx_precompile_lane; sd zero, 0(t0); j .Lbv_mtx_is_contract\n" ++
  ".Lbv_mtx_is_contract:\n" ++
  -- #10695 INVARIANT: EVERY PATH REACHING `dispatch_tx_runtime_code` MUST FIRST STORE THIS
  -- TRANSACTION'S block_access_index (i+1; EIP-7928: 0 for system, i+1 for the i-th user tx,
  -- fork.py:1030) INTO `current_block_access_index`.  Exactly four stores satisfy it: the one
  -- below, the EOA-recipient path (.Lbv_mtx_recipient_lookup_resolved), the creation path
  -- (.Lbv_mtx_creation_access_done), and the single-tx lane (.Lbv_stx_checks_done).
  --
  -- This comment is the whole gate, deliberately.  An emitted-asm path enumeration would need a
  -- codegen artifact at check time for an invariant unlikely to regress once fixed, and what
  -- failed here was never a missing check -- it was a comment that said the opposite of what the
  -- code did, so a reader who came to ask whether attribution was handled found prose saying yes.
  --
  -- THIS PATH IS THE ONE THAT DID NOT STAMP IT.  The four recipient-code-hash `bne`s above jump
  -- straight to this label, PAST the EOA-recipient store, so a contract recipient -- the only tx
  -- class that can execute SSTORE at all -- reached `dispatch_tx_runtime_code` with the index
  -- still holding its static default 1, or whatever the last EOA/creation tx left behind.  The
  -- SSTORE handler stamps `exec_log_txindex[row]` from it (.Lsstore_append_entry), so those rows
  -- carried a value the transaction never wrote.  Measured: 398/400 rows disagreeing with i+1.
  --
  -- And the comment that used to sit here asserted the stamp WAS on this path, quoting the same
  -- EIP-7928 rule, while the next emitted line stamped `dtrc_use_pre_header`, an unrelated flag.
  --
  -- The same old comment also called the consumers "still-unwired".  They are not:
  -- `exec_log_txindex` is the a4 base of `bal_all_accounts_tuple_sequences_consistent_skip_list`
  -- at both the mtx and single-tx call sites, and a nonzero return from either rejects the block.
  -- Nothing objects today only because that comparator's per-change loop iterates zero times
  -- (#10681) -- i.e. IT CANNOT BE MADE NON-VACUOUS UNTIL THIS STAMP EXISTS, because the first
  -- thing a working comparator does is read a transaction index no contract tx ever wrote.
  --
  -- Demonstrated end to end on the EEST case `bal_cross_tx_storage_write[tx2_reverts_to_zero]`,
  -- two transactions to the same contract (`0x600035600055`), whose declared BAL carries
  -- blockAccessIndex 1 and 2 for the written slot.  Probing the max/min index the SSTORE handler
  -- actually stamps, over two appends: WITHOUT this store min=max=1 (both transactions tagged 1);
  -- WITH it min=1 max=2, matching the fixture's declared indices.  Verdict-neutral on that case.
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
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
  -- The shared dispatcher owns the complete post-preparation body checkpoint.
  "  la t0, runtime_tx_auth_sender_ptr; la t1, bv_mtx_sender_addr; sd t1, 0(t0); la a0, bv_mtx_ctx; ld a1, 80(s0); ld a2, 88(s0); jal ra, dispatch_tx_runtime_code\n" ++
  "  la t0, create_nonce_table_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, exec_code_effect_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, account_state_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- `write_sets_incorporate_tx` clears the transaction-local latch after a
  -- successful merge.  Test it before either success or rollback can discard
  -- the evidence: a full tx map is an incomplete execution record, never a
  -- reason to silently skip the storage comparison.
  "  la t0, tx_storage_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, tx_account_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- GH #10731: the READ-side latches, which were set and never examined. Same
  -- reasoning as the write-side pair above -- a full read map is an incomplete
  -- execution record -- and the same failure label, so this completes the existing
  -- list rather than introducing a reject path.
  --
  -- ONE ASYMMETRY WORTH KNOWING: unlike the write-side latches, these have NO clear
  -- site (`read_sets_discard_tx` clears the counts, not the flags), so a set flag is
  -- STICKY for the rest of the block rather than per-transaction. Since the outcome is
  -- a reject either way, stickiness can only be more conservative — but it is a real
  -- difference from the lines above and not an oversight in this change.
  "  la t0, tx_storage_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, tx_account_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, tx_code_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, bv_dispatch_runtime_status; sd a0, 0(t0)\n  la t1, dtrc_use_pre_header; sd zero, 0(t1)\n" ++
  -- The shared dispatcher returns 8 only after a status-2 recipient lookup
  -- completed its common preparation prefix.  This is a verifier failure, not
  -- an executable body or a second settlement path.
  "  li t1, 8; beq a0, t1, .Lbv_mtx_recipient_unresolvable_fail\n" ++
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
  ".Lbv_mtx_effects_kept:\n" ++
  -- `move_ether` is now the shared dispatcher's one post-body-mark producer:
  -- it records sender debit and recipient credit together, with rollback rather
  -- than this former receipt-status guard deciding failed-body behaviour.
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
  -- r59nm: the storage_writes map commits on TX STATUS ALONE, decided here and
  -- NOT inside account_state_commit_pending.  The AccountState gate below also
  -- commits when `runtime_tx_post_preparation_reached` is set, and that flag does NOT
  -- mean an authorization was applied -- it marks the dispatcher reaching the
  -- POST-PREPARATION COVERAGE POINT, which nearly every transaction whose body
  -- fails after preparation reaches.  Merging storage on that disjunct promoted
  -- failed transactions' writes into the block map (measured: sstore_0to0to_x
  -- d5-g0, status 0, flag 1, the reverted write present in the block map).
  -- The spec has no such carve-out for storage: incorporate_tx_into_block runs
  -- for committing transactions, and a failed one contributes nothing
  -- (state_tracker.py:832; fresh TransactionState per tx at fork.py:1043).
  -- Reads are deliberately untouched either way -- same event, opposite
  -- treatment, which is why there are two containers.
  "  addi sp, sp, -16; sd ra, 0(sp)\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 3; la t2, bv_tx_status_arr; add t2, t2, t1; ld t2, 0(t2)\n" ++
  "  beqz t2, .Lbv_mtx_storage_drop\n" ++
  "  jal ra, write_sets_incorporate_tx; j .Lbv_mtx_storage_done\n" ++
  ".Lbv_mtx_storage_drop:\n" ++
  "  jal ra, write_sets_discard_tx\n" ++
  ".Lbv_mtx_storage_done:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16\n" ++
  -- The block-lifetime map can overflow while incorporating a successful tx.
  -- Its producer returns normally to preserve the caller frame, so consume the
  -- latched failure at the transaction boundary rather than serializing a
  -- truncated block map later.
  "  la t0, storage_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- The debit was materialized before execution; apply the spec's later
  -- sender `create_ether` refund before AccountState commits this transaction.
  blockVerdictMtxRecordSenderRefund ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 3; la t2, bv_tx_status_arr; add t2, t2, t1; ld t2, 0(t2); bnez t2, .Lbv_mtx_code_commit; la t0, runtime_tx_post_preparation_reached; ld t2, 0(t0); bnez t2, .Lbv_mtx_code_commit\n" ++
  -- `process_message` restores the preparation snapshot when preparation
  -- itself halts.  The map's direct auth producer mirrors that control-flow
  -- fact with its own cursor, rather than reusing the dead frame checkpoint.
  "  la t0, account_writes_auth_prepare_mark; ld a0, 0(t0); jal ra, account_writes_restore_frame\n" ++
  "  la t0, account_state_pending_count; sd zero, 0(t0); la t0, account_state_created_count; sd zero, 0(t0); la t0, account_state_delete_count; sd zero, 0(t0)\n" ++
  -- `blockVerdictMtxRecordSenderRefund` and the rollback helper both use
  -- caller-saved a1/a2.  The snapshot ABI takes this transaction's captured
  -- slice, not the cumulative `bv_user_storage_log`: a preparation halt has
  -- no such rows, so restore base + length zero explicitly.  Do not reconstruct
  -- from capture counters, which may still describe tx N-1 (and must remain
  -- available to the later BAL consumer through the cumulative arena).
  "  la a1, bv_user_storage_log; li a2, 0\n" ++
  "  j .Lbv_mtx_code_commit_done\n" ++
  ".Lbv_mtx_code_commit:\n" ++
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
  -- Body effects are already rolled back to the undo mark above on status=0.
  -- The coinbase fee is appended after that rollback and survives either
  -- receipt status, so incorporate once here without a second status gate.
  blockVerdictMtxCoinbaseFeeEffect ++
  "  jal ra, account_state_commit_pending; bnez a0, .Lbv_mtx_bail\n" ++
  -- `incorporate_tx_into_block` promotes all three read sets unconditionally:
  -- storage, account, and code reads survive a failed transaction even when
  -- its AccountState commit is bypassed.  This join follows the spec order:
  -- sender refund, coinbase fee, then incorporation.  In particular the fee
  -- helper's balance lookup records a coinbase account read even when its
  -- priority-fee credit is zero; promote that final per-transaction read at
  -- this transaction's incorporation boundary.
  -- The committed-storage snapshot above is complete; retain the existing
  -- caller-save wrapper because this function still needs its outer `ra`.
  "  addi sp, sp, -32; sd ra, 0(sp); sd a1, 8(sp); sd a2, 16(sp); jal ra, read_sets_incorporate_tx; ld ra, 0(sp); ld a1, 8(sp); ld a2, 16(sp); addi sp, sp, 32\n" ++
  -- Consume the merge latches immediately after the merge that sets them.
  "  la t0, storage_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, account_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, code_reads_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- `update_builder_from_tx` precedes `incorporate_tx_into_block` in the spec:
  -- the tx account-map reader must see the block-cumulative *pre-tx* baseline
  -- before incorporation overwrites it and clears the tx map.  The helper reads
  -- `current_block_access_index` (bv_mtx_i + 1), not the unwritten builder-local
  -- BAI cell.
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  "  la t0, account_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0); j .Lbv_mtx_loop\n" ++
  ".Lbv_mtx_done:\n" ++
  -- EIP-7928's block access index advances once more for the post-transaction
  -- system/withdrawal boundary.  The producers already dual-record into the
  -- transaction AccountWrite map; make this N+1 boundary feed the same builder
  -- walk and block-level incorporate path before receipts consume the result.
  -- EIP-4895 withdrawals are a block-level producer, not a transaction effect.
  -- Run the existing recorder here so its 112-byte execution record and
  -- transaction AccountWrite entry are present for the N+1 builder walk.
  "  jal ra, block_verdict_withdrawal_nonstorage_effects; bnez a0, .Lbv_bal_nonstorage_fail\n" ++
  "  jal ra, read_sets_incorporate_tx\n" ++
  "  la t0, bv_tx_count; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0)\n" ++
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  "  la t0, account_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- GH #10866 / GH #10701: the STORAGE half of this same N+1 boundary.  The four
  -- lines above have carried the non-storage half since GH #10875; storage was the
  -- one open cell of the phase-by-field matrix (GH #10701).
  --
  -- The end-of-block system calls' writes were made much earlier, in the requests
  -- phase, and discarded there so transaction 1 could not claim them.
  -- `replay_system_storage_writes_at_bai` re-presents them from the side arena that
  -- kept them, and HERE is the only place that works: the emit inside
  -- `write_sets_incorporate_tx` filters net-zero against the BLOCK container, and
  -- only after the loop does that container hold the transactions' writes.  Every
  -- declared N+1 row measured on 23100 and 23725 is `pre=0 -> post=0` with a
  -- transaction writing 1 to the same slot first, so the baseline is the whole
  -- question -- emitting in the requests phase produced 1 of 3 and 0 of 8.
  --
  -- `write_sets_incorporate_tx` rather than a bare emit: past the transactions,
  -- merging is what the spec does (`fork.py:858-859`, `:1226`) and one call already
  -- emits, merges and clears in that order.
  --
  -- It reads `current_block_access_index`, set to N+1 three lines above, so the
  -- storage and non-storage halves cannot disagree about the index.
  "  jal ra, replay_system_storage_writes_at_bai\n" ++
  "  jal ra, write_sets_incorporate_tx\n" ++
  "  la t0, storage_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
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
  -- `sttc_nonce` is this transaction's pre-inclusion nonce, exactly the
  -- CREATE input. Do not copy the spec's explicit minus-one: it compensates
  -- for a different stored-post-nonce mechanism.
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
  -- The shared processor owns the post-preparation body checkpoint; creation
  -- keeps only its routing/header setup here.
  "  la t0, bv_mtx_i; ld t1, 0(t0); addi t1, t1, 1; la t0, current_block_access_index; sd t1, 0(t0); li t0, 1; la t1, dtrc_use_pre_header; sd t0, 0(t1)\n" ++
  "  la t0, bv_creation_output_mode; li t1, 1; sd t1, 0(t0); la t0, bv_mtx_i; ld t1, 0(t0); la t0, bv_creation_output_index; sd t1, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; la t0, bv_exec_p; ld a1, 0(t0); jal ra, block_verdict_creation_runtime\n" ++
  "  la t0, bv_creation_output_mode; sd zero, 0(t0); la t0, dtrc_use_pre_header; sd zero, 0(t0)\n" ++
  "  bnez a0, .Lbv_mtx_creation_unsupported\n" ++
  -- Re-key the shared mtx postlude to the created account.  The context is
  -- replaced on the next loop iteration, and only its address slot is read by
  -- the postlude's committed-storage snapshot.
  "  la t0, bv_create_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_creation_key_copy:\n  beqz t2, .Lbv_mtx_creation_post; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_creation_key_copy\n" ++
  ".Lbv_mtx_creation_post:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t0, t1, 3; la t3, bv_tx_status_arr; add t3, t3, t0; ld a4, 0(t3)\n" ++
  -- The shared creation runner has populated this transaction's indexed
  -- gas/status/log result.  Rejoin the same finalization path as a completed
  -- CALL: it consumes those indexed results, incorporates the transaction, and
  -- advances `bv_mtx_i` before the block-level receipt materializer runs.
  "  j .Lbv_mtx_effects_kept\n" ++
  ".Lbv_mtx_creation_unsupported:\n" ++
  -- A failed/unsupported creation leaves only the preceding exact prefix in
  -- the strided arrays.  Preserve that prefix for the remaining gas check;
  -- successful creations rejoin `.Lbv_mtx_effects_kept` above instead.
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

-- GH #10866: the N+1 storage replay is pinned WITH the incorporate that consumes it
-- and must appear exactly once -- inside the loop it would re-present the system
-- writes on every transaction.  The sibling occurrence is guarded in
-- `BlockVerdictEoaBodyEffectReconcile`; the two sites are mutually exclusive at run
-- time, so both must exist and neither may be doubled.
#guard (blockVerdictMtxRuntimeLoop.splitOn
  "  jal ra, replay_system_storage_writes_at_bai\n  jal ra, write_sets_incorporate_tx\n").length == 2

end EvmAsm.Codegen
