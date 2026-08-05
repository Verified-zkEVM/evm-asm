/-
  EvmAsm.Codegen.Programs.BlockVerdictMtxRuntime

  Extracted multi-transaction runtime-gas fragment for block_verdict.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams
import EvmAsm.Codegen.Programs.BlockVerdictMtxTail
import EvmAsm.Codegen.Programs.BlockVerdictSimpleTransferGas
import EvmAsm.Codegen.Programs.BlockVerdictReceiptGate
import EvmAsm.Codegen.Programs.BlockVerdictMtxCoinbase
import EvmAsm.Codegen.Programs.BlockVerdictDepositFallback
import EvmAsm.Codegen.Programs.BlockVerdictCreationStage
import EvmAsm.Codegen.Programs.AccountWriteMap

namespace EvmAsm.Codegen

/-- Reset the transaction-local EIP-7702 preparation cells at the common MTx
    boundary.  This is the only owner of the reset: creation, contract, and
    EOA routes all pass through the loop header, while the type-4 dispatcher
    repopulates the cells only when this transaction carries authorizations. -/
private def blockVerdictMtxTxPreparationReset : String :=
  "  la t0, runtime_tx_auth_state_refund; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_state_charge; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_regular_refund; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_top_frame_regular_gas; sd zero, 0(t0)\n" ++
  "  la t0, teer_success_count; sd zero, 0(t0)\n" ++
  "  la t0, create_deposit_witness_incomplete_flag; sd zero, 0(t0)\n" ++
  "  la t0, create_deposit_malformed_flag; sd zero, 0(t0)\n"

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
  "  la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; jal ra, account_state_latest_balance_block\n" ++
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

/-- Apply the post-execution sender refund, then publish its resulting live
    balance.  `fork.py:1169` calls `create_ether(sender, gas_refund_amount)`:
    this is a one-sided AccountState credit, not a `move_ether` transfer.  The
    upfront debit is already materialized before dispatch.  Preserve that
    state transition first, then read its final post-balance for the BAL
    producer rather than reconstructing a BAL value from refund arithmetic. -/
private def blockVerdictMtxRecordSenderRefund : String :=
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t1, t1, 3\n" ++
  "  la t0, bv_mtx_ctx; ld a0, 40(t0); la t2, bv_mtx_gas_left; add t2, t2, t1; ld a1, 0(t2); la t2, bv_mtx_refund; add t2, t2, t1; ld a2, 0(t2); la t2, bv_mtx_calldata; add t2, t2, t1; ld a3, 0(t2); jal ra, tx_gas_result_increments\n" ++
  "  bnez a0, .Lbv_mtx_sr_done\n" ++
  "  la t0, bv_mtx_ctx; ld t1, 40(t0); bgtu a2, t1, .Lbv_mtx_bail; sub a1, t1, a2\n" ++
  "  la a0, bv_fee_egp_scratch; la a2, bv_pending_upfront_sender_post; jal ra, u256_mul_u64_be\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; jal ra, account_state_latest_balance\n" ++
  "  beqz a0, .Lbv_mtx_bail  # no fallback: the staged upfront debit retained the sender entry\n" ++
  "  la a0, bv_pending_upfront_sender_pre; la a1, bv_pending_upfront_sender_post; la a2, bv_pending_upfront_sender_post; jal ra, u256_add_be\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  -- Apply the execution-spec's `create_ether` transition before emitting the
  -- BAL row.  The BAL producer below deliberately re-reads this final state.
  "  la t0, sttc_nonce; ld a3, 0(t0); addi a4, a3, 1; la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; la a2, bv_pending_upfront_sender_post; jal ra, account_state_record_nonstorage\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
  "  la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_post; jal ra, account_state_latest_balance\n" ++
  "  beqz a0, .Lbv_mtx_bail  # the preceding AccountState credit must be observable\n" ++
  "  la t0, sttc_nonce; ld a3, 0(t0); addi a4, a3, 1; la a0, bv_mtx_sender_addr; la a1, bv_pending_upfront_sender_pre; la a2, bv_pending_upfront_sender_post; jal ra, record_nonstorage_effect_after_account_state\n" ++
  "  bnez a0, .Lbv_mtx_bail\n" ++
".Lbv_mtx_sr_done:\n"

/-! Gate the pre-user system-storage seed on the same code-presence predicate as
    `process_unchecked_system_transaction`.  The MTx lane seeds the canonical
    block map before dispatch so user SLOADs can resolve the EIP-2935/4788
    startup writes.  An absent or codeless system contract executes no code and
    therefore must not leave a storage-map row behind.  `block_state_root`
    repeats this check for its terminal descriptors; clearing only those
    descriptors cannot retract a row already inserted into the canonical map.

    The output account buffer is shared between the two lookups, and every
    nonzero lookup result is treated as "not a writable system contract" here.
    The terminal root pass remains authoritative for malformed witness handling;
    this early guard only prevents a speculative map seed. -/
private def blockVerdictMtxGateSystemStorageSeed : String :=
  "  la a0, bsr_addr_2935; li a1, 20; ld a2, 8(s0); ld a3, 16(s0); ld a4, 80(s0); ld a5, 88(s0); la a6, bsr_sys_acct; jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_sys2935_skip\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_empty_code_hash; li t2, 32\n" ++
  ".Lbv_mtx_sys2935_code_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_sys2935_ident\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbv_mtx_sys2935_code_cmp\n" ++
  ".Lbv_mtx_sys2935_skip:\n" ++
  "  la t0, swd_2935_vlen; sd zero, 0(t0); j .Lbv_mtx_sys2935_present\n" ++
  ".Lbv_mtx_sys2935_ident:\n" ++
  "  # GH #11431: non-empty deployed code_hash must be the canonical EIP-2935 hash.\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_canonical_2935_code_hash; li t2, 32\n" ++
  ".Lbv_mtx_sys2935_ident_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_syscode_identity_fail\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbv_mtx_sys2935_ident_cmp\n" ++
  ".Lbv_mtx_sys2935_present:\n" ++
  "  la a0, bsr_addr_4788; li a1, 20; ld a2, 8(s0); ld a3, 16(s0); ld a4, 80(s0); ld a5, 88(s0); la a6, bsr_sys_acct; jal ra, account_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_sys4788_skip\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_empty_code_hash; li t2, 32\n" ++
  ".Lbv_mtx_sys4788_code_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_mtx_sys4788_ident\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbv_mtx_sys4788_code_cmp\n" ++
  ".Lbv_mtx_sys4788_skip:\n" ++
  "  la t0, swd_4788_vlen; sd zero, 0(t0); la t0, swd_4788_root_vlen; sd zero, 0(t0); j .Lbv_mtx_sys4788_present\n" ++
  ".Lbv_mtx_sys4788_ident:\n" ++
  "  # GH #11431: non-empty deployed code_hash must be the canonical EIP-4788 hash.\n" ++
  "  la t0, bsr_sys_acct; addi t0, t0, 72; la t1, cd_canonical_4788_code_hash; li t2, 32\n" ++
  ".Lbv_mtx_sys4788_ident_cmp:\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_syscode_identity_fail\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; bnez t2, .Lbv_mtx_sys4788_ident_cmp\n" ++
  ".Lbv_mtx_sys4788_present:\n"

/- Materialize the process_transaction sender debit when the shared callable
   dispatcher halts exceptionally before its normal pending-seed and MTx
   postlude. The tuple is already authenticated and computed by
   blockVerdictMtxStageSenderUpfront; this helper performs no second fee
   calculation. -/
private def blockVerdictMtxOogMaterialize : String :=
  "block_verdict_mtx_oog_materialize:\n" ++
  "  addi sp, sp, -16; sd ra, 0(sp)\n" ++
  -- Preparation ExceptionalHalt takes the dispatcher-unsupported path before
  -- the normal effects-kept postlude.  Re-enter the one shared finalizer
  -- first, so it restores the auth snapshot and append-only effect cursors;
  -- then restore the transaction account map to the mark taken after sender
  -- inclusion.  The ordinary OOG path has no auth snapshot to roll back.
  "  la t0, runtime_tx_auth_phase_halted; ld t1, 0(t0); beqz t1, .Lbv_mtx_oog_normal\n" ++
  "  la t0, bv_mtx_i; ld a0, 0(t0); li a1, 0; jal ra, block_verdict_tx_state_gas_inline_finalize\n" ++
  "  la t0, account_writes_auth_prepare_mark; ld a0, 0(t0); jal ra, account_writes_restore_frame\n" ++
  ".Lbv_mtx_oog_normal:\n" ++
  "  la t0, bv_pending_upfront_balance_flag; ld t1, 0(t0); beqz t1, .Lbv_mtx_oog_done\n" ++
  "  jal ra, dispatcher_seed_pending_upfront_sender_balance\n" ++
  "  jal ra, account_state_commit_pending\n" ++
  "  bnez a0, .Lbv_mtx_oog_done\n" ++
  "  jal ra, account_writes_emit_builder_tx\n" ++
  "  jal ra, account_writes_incorporate_tx\n" ++
  ".Lbv_mtx_oog_done:\n" ++
  "  ld ra, 0(sp); addi sp, sp, 16; ret\n"

/-- Gated multi-transaction runtime-gas loop fragment.  Every block falls
    through to the MTx loop, which iterates zero times on an empty block;
    the former `bv_tx_count == 0` branch to `.Lbv_recipient_nc_done` and the
    `.Lbv_singletx` hop before it were duplicate tests of the same condition,
    both now removed. -/
def blockVerdictMtxRuntimeLoop : String :=
  -- Multi-transaction runtime gas loop (every non-empty block enters MTx).
  --
  -- bvgr_runtime_count contract (live; do not delete — explains 11407 fallback):
  -- zeroed at block_verdict entry. Set to bv_tx_count ONLY on success paths after
  -- full MTx completion (.Lbv_mtx_publish). Any bail (.Lbv_mtx_bail,
  -- .Lbv_mtx_dispatch_unsupported, EOA/unsupported/capacity/dispatch-miss, parse
  -- error, etc.) jumps to .Lbv_after_tx_gas_precharge with count left 0, so
  -- arena_prepare sees a short count and the exact prior-state / block-gas path
  -- is skipped (conservative). That count-left-0 behaviour is real.
  --
  -- #11183 / maintainer proof-architecture ruling: bal_txs_independent and the
  -- bv_deposit_capture_only route are RETIRED. Spec has one tx loop (fork.py:913)
  -- and no deposit-vs-capture branch; deposits come from post-exec receipt logs.
  -- Guest must not read supplied BAL body except to hash it; extra reject-only
  -- checks need a collision assumption. The capture-only shortcut (skip
  -- MtxValidationTail after root) had no spec counterpart — branch deleted, not
  -- re-sourced. Deposit requests stay on the log parse + DirectDepositFallback path.
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
  --  * `i3djw_skip_list` was BUILT and never CONSULTED; removed under #10685
  --    (0 refs). The list the live path passes is `bv_mtx_skip_list`, at the
  --    `BlockVerdictMtxTail` call to
  --    `bal_all_accounts_storage_consistent_skip_list`.
  --  * the old single-tx entry and its contract/creation/recipient-exactness
  --    body were audited on the emitted image before removal.  The closure was
  --    seeded from `block_verdict`, `block_verdict_mtx_oog_materialize`, and
  --    the live MTx precompile jump at `.Lbv_tx_gas_precharge_pc0_prefix`;
  --    the 235-label region had 189 reachable and 46 unreachable labels.  No
  --    `la`, `auipc`, `jalr`, dispatch-table entry, or `.dword` materialized an
  --    address into the retired region.  The precompile selector/publish tail
  --    is retained and emitted immediately after this loop because that is the
  --    only live interior entry.
  --  * the surviving guard `bv_pending_upfront_balance_flag` remains a live
  --    dispatcher consumer for #10698; the retired single-tx producer was not
  --    its only producer on current main (the MTx producer is present).
  -- #10591 routing: every block (including zero-tx) goes through the MTx
  -- loop; the loop iterates zero times on an empty block (matches
  -- execution-specs fork.py:913-914, which has no empty-block special case).
  "  la t0, bv_tx_count; ld t0, 0(t0)\n" ++
  "  li t1, " ++ toString bvMtxActiveTxCap ++ "; bgtu t0, t1, .Lbv_mtx_bail         # active loop capacity\n" ++
  -- #11183: zero deposit-route cells (retired branch; no setter remains).
  "  la t1, bv_deposit_capture_only; sd zero, 0(t1); la t1, bv_deposit_runtime_capture_complete; sd zero, 0(t1)\n" ++
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
  "  bnez a0, .Lbv_sender_count_table_fail\n" ++  -- was 40 → 68
  "  la t0, bv_mtx_skip_idx; sd zero, 0(t0)\n" ++
  ".Lbv_mtx_sender_count_zero_loop:\n" ++
  "  la t0, bv_mtx_skip_idx; ld t1, 0(t0); la t2, bv_b1_sender_count; ld t2, 0(t2); bgeu t1, t2, .Lbv_mtx_sender_count_zero_done\n" ++
  "  li t3, 40; mul t3, t1, t3; la t4, bv_b1_sender_table; add t4, t4, t3; sd zero, 32(t4)\n" ++
  "  addi t1, t1, 1; la t0, bv_mtx_skip_idx; sd t1, 0(t0); j .Lbv_mtx_sender_count_zero_loop\n" ++
  ".Lbv_mtx_sender_count_zero_done:\n" ++
  -- Frozen S1 authority materialize RETIRED (was dead after j .Lbv_mtx_state_init;
  -- nm: eas_write_entry + eip7702_authority_state_materialize absent from image).
  -- Live 7702 delegated_before_tx is eip7702_authority_asof → auth_state_prepare
  -- (AccountState durable + header code), NOT bv_eip7702_authority_table+40.
  -- MTx sender InvalidSender gate below is a separate reject predicate (fork.py:668-677).
  ".Lbv_mtx_state_init:\n" ++
  "  la t0, bv_mtx_i; sd zero, 0(t0)\n" ++
  -- Execution AccountState is block-lived in the sequential lane. The callable
  -- dispatcher resets transaction-local pending overlays, including
  -- `account_state_pending_count`; it does not preserve that AccountState
  -- journal across dispatches. This reset is the live durability boundary in
  -- GH #10876: sender effects needed after dispatch must be materialized in
  -- durable state rather than left in the pending journal. Durable state and
  -- retained comparator bytes survive until this loop finishes.
  -- AccountState is the sole emitted execution code/existence model for every
  -- block, including the one-transaction case.  The immutable witness is
  -- consulted only after its pending and durable overlays miss; CodeState
  -- names are compatibility aliases, not a separate table.
  -- `runtime_mtx_active` is a reserved compatibility cell only.  The
  -- universal dispatcher no longer reads or writes it; retaining the slot
  -- keeps the established data layout stable for existing image pins.
  "  la t0, runtime_tx_oog_hook; la t1, block_verdict_mtx_oog_materialize; sd t1, 0(t0); la t0, account_state_durable_count; sd zero, 0(t0); la t0, account_state_pending_count; sd zero, 0(t0); la t0, account_state_created_count; sd zero, 0(t0); la t0, account_state_delete_count; sd zero, 0(t0); la t0, account_state_overflow; sd zero, 0(t0)\n" ++
  "  la t0, exec_code_effect_count; sd zero, 0(t0); la t0, exec_code_effect_next; sd zero, 0(t0); la t0, exec_code_effect_overflow; sd zero, 0(t0)\n" ++
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
  -- execution-specs runs the EIP-4788 and EIP-2935 system transactions before
  -- the user transaction loop.  Derive the same three descriptors here and
  -- seed the canonical block map before any h_SLOAD can consult it.  The
  -- row helper's vlen guards preserve the zero-value/deletion no-op cases;
  -- its seed-only mode does not publish side-log or BAL rows until the
  -- terminal state-root replay.
  "  la t0, bv_exec_p; ld a0, 0(t0); addi a0, a0, -60; jal ra, system_write_descriptors\n" ++
  "  # GH #11378: the EIP-2935 system transaction tracks the parent ancestor\n" ++
  "  # (amsterdam fork.py:908); mark = max(mark, 1).\n" ++
  "  la t0, evm_oldest_ancestor_offset; ld t1, 0(t0); bnez t1, .Lbv_mtx_oao_2935_done\n" ++
  "  li t1, 1; sd t1, 0(t0)\n" ++
  ".Lbv_mtx_oao_2935_done:\n" ++
  blockVerdictMtxGateSystemStorageSeed ++
  "  li t1, 1; la t0, bv_system_storage_map_seed_only; sd t1, 0(t0)\n" ++
  "  jal ra, append_modeled_system_storage_tuple_rows\n" ++
  "  mv t2, a0; la t0, bv_system_storage_map_seed_only; sd zero, 0(t0)\n" ++
  "  bnez t2, .Lbv_mtx_bail\n" ++
  ".Lbv_mtx_loop:\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); la t2, bv_tx_count; ld t2, 0(t2); beq t1, t2, .Lbv_mtx_done\n" ++
  -- Every supported route shares this transaction boundary.  Clear staged
  -- authorization state before extracting the next context; a type-4
  -- dispatcher repopulates it, while ordinary and creation transactions do
  -- not.  Keeping the reset here prevents a prior authorization's AUTH_BASE
  -- or ACCOUNT_WRITE cells from becoming a later transaction's preparation.
  blockVerdictMtxTxPreparationReset ++
  -- The dispatcher resets this marker only when it is reached.  Every MTx
  -- iteration must begin phase-zero as well: a pre-dispatch rejection or an
  -- EOA/non-runtime route otherwise inherits a previous transaction's
  -- successful preparation and incorrectly retains staged authorization gas.
  "  la t0, runtime_tx_post_preparation_reached; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_phase_halted; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_auth_prepared; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_i; ld t1, 0(t0); slli t2, t1, 3; la t0, bv_tx_auth_phase_applied_arr; add t0, t0, t2; sd zero, 0(t0)\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; sd zero, 0(t0)\n" ++
  "  la t0, bv_mtx_recipient_lookup_deferred; sd zero, 0(t0)\n" ++
  -- The tuple is one-shot.  A pre-dispatch terminal route must not leak an
  -- unconsumed predecessor tuple into this transaction.
  "  la t0, bv_pending_upfront_balance_flag; sd zero, 0(t0)\n" ++
  "  la a0, bv_mtx_ctx; mv a1, t1; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_ctx; ld t2, 0(t0); bnez t2, .Lbv_mtx_bail\n" ++
  -- `dispatch_tx_runtime_code` consumes the context's +32 base-fee pointer
  -- when staging `tx_env.gas_price` for GASPRICE.  `multi_tx_nth_context`
  -- intentionally leaves this per-call input empty; the block base fee was
  -- already decoded into `bv_mtx_base_fee_be` for the MTx fee-validity gate
  -- above.  Supplying that same authenticated buffer here keeps the runtime
  -- environment aligned with execution-specs `process_transaction`, which
  -- installs `effective_gas_price` in `tx_env` before `process_message`.
  "  la t0, bv_mtx_ctx; la t1, bv_mtx_base_fee_be; sd t1, 32(t0)\n" ++
  -- bmvmx.5 (fee-validity hoist, multi-tx): same PATH-INDEPENDENT check_transaction
  -- fee-validity test as the single-tx gate (max_fee>=base_fee / priority<=max_fee),
  -- run per tx in the mtx loop. bv_mtx_ctx holds tx ptr@8 / len@16 (simple_transfer layout,
  -- BlockVerdictMultiTx.lean:38); base_fee comes from bv_mtx_base_fee_be (computed above —
  -- record+32 is NOT filled by multi_tx_nth_context). Placed before the contract/EOA-recipient
  -- routing so it covers EVERY status-0 tx the loop reaches. tx_effective_gas_pricing returns
  -- 1 when transaction-type or canonical fee extraction fails, 2 when priority>max_fee, and 3
  -- when max_fee<base_fee. execution-specs decodes every transaction unconditionally before
  -- applying the block, so all three are transaction-validity failures and reject here. Status 4
  -- is the separately-proven-unreachable effective-price overflow case. (t1 is reset at the
  -- code-hash compare / reloaded from bv_mtx_i later; s0-s3 preserved by the call.)
  "  la t2, bv_mtx_ctx\n" ++
  "  ld a0, 8(t2); ld a1, 16(t2); la a2, bv_mtx_base_fee_be\n" ++   -- tx ptr, tx len, block base_fee (BE)
  "  la a3, bv_fee_egp_scratch; la a4, bv_fee_prio_scratch\n" ++
  "  jal ra, tx_effective_gas_pricing\n" ++
  "  li t1, 1; beq a0, t1, .Lbv_fee_invalid_fail\n" ++          -- pricing extraction failed -> reject
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
  -- Resolve the sender's pre-transaction account with the same precedence as
  -- execution-specs `_get_pre_tx_account`: block-cumulative account writes,
  -- then the authenticated parent-state account.  In particular, an account
  -- created and funded by an earlier transaction has a valid balance-only
  -- block row and an absent parent account; `account_resolve_pre_state`
  -- returns that row's balance and the absent account's nonce zero.  The old
  -- latest-nonce/header pair treated the missing nonce bit as a total lookup
  -- failure and skipped the gas/blob debit before this transaction's stage.
  -- (block_access_lists.py:583-600, fork.py:656-667.)
  "  la a0, bv_mtx_sender_addr; la a1, bv_mtx_sender_acct; ld a2, 8(s0); ld a3, 16(s0); ld a4, 80(s0); ld a5, 88(s0); jal ra, account_resolve_pre_state\n" ++
  "  bnez a0, .Lbv_sender_resolve_fail\n" ++  -- was 40 → 69
  "  la t0, bv_mtx_sender_acct; ld t0, 0(t0)\n" ++
  "  la t1, sttc_nonce; ld t1, 0(t1)\n" ++                      -- t1 = tx.nonce
  "  bne t1, t0, .Lbv_sender_nonce_fail\n" ++                   -- tx.nonce != current sender nonce (code 40 kept)
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
  -- fork.py:668-677 InvalidSender ("not EOA"): get_code(sender) then require
  -- EMPTY_CODE_HASH or is_valid_delegation.  Missing marker preimage (status 5
  -- with non-empty hash) rejects — closes 02970 missing_sender_delegation_marker.
  -- InvalidSender gate (independent of 7702 authority-table materialize).
  -- Layout: have_code first, empty-hash compare last so #11520 gate window is clean.
  "  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0)\n" ++
  "  la a2, bv_mtx_sender_addr\n" ++
  "  la t0, bv_witness_state_ptr; ld a3, 0(t0); la t0, bv_witness_state_len; ld a4, 0(t0)\n" ++
  "  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)\n" ++
  "  jal ra, code_at_header_state_root\n" ++
  "  li t0, 1; beq a0, t0, .Lbv_mtx_sender_eoa_ok\n" ++          -- absent → empty EOA
  "  li t0, 5; beq a0, t0, .Lbv_mtx_sender_st5\n" ++
  "  bnez a0, .Lbv_sender_nonce_fail\n" ++                       -- 2/3/4 malformed
  -- status 0: is_valid_delegation (len 23 + 0xef0100)
  "  la t0, cahsr_code_length; ld t0, 0(t0); li t1, 23; bne t0, t1, .Lbv_sender_nonce_fail\n" ++
  "  la t0, svf_codes_ptr; ld t0, 0(t0); la t1, cahsr_code_offset; ld t1, 0(t1); add t0, t0, t1\n" ++
  "  lbu t1, 0(t0); li t2, 239; bne t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  lbu t1, 1(t0); li t2, 1; bne t1, t2, .Lbv_sender_nonce_fail\n" ++
  "  lbu t1, 2(t0); bnez t1, .Lbv_sender_nonce_fail\n" ++
  "  j .Lbv_mtx_sender_eoa_ok\n" ++
  ".Lbv_mtx_sender_st5:\n" ++
  -- status 5: only EMPTY_CODE_HASH is acceptable (raise→reject #11520)
  "  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash\n" ++
  "  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lbv_sender_nonce_fail\n" ++
  "  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lbv_sender_nonce_fail\n" ++
  "  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbv_sender_nonce_fail\n" ++
  "  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbv_sender_nonce_fail\n" ++
  "  j .Lbv_mtx_sender_eoa_ok\n" ++
  ".Lbv_mtx_sender_eoa_ok:\n" ++
  -- `process_transaction` increments the sender nonce before preparation.
  -- Publish that monotone execution fact both to the durable execution overlay
  -- and to the transaction-local BAL map. This is deliberately before the
  -- body rollback checkpoint: a failed body keeps the transaction nonce, while
  -- the checkpoint removes later body writes. Balance has later value, refund,
  -- and coinbase-credit writes, so it needs its own complete state transition
  -- rather than an inclusion-time snapshot here.
  "  la t0, sttc_nonce; ld a1, 0(t0); addi a1, a1, 1; la a0, bv_mtx_sender_addr; jal ra, account_state_publish_sender_inclusion; bnez a0, .Lbv_sender_inclusion_fail\n" ++  -- was 40 → 71
  "  la t0, sttc_nonce; ld a2, 0(t0); addi a2, a2, 1; la a0, bv_mtx_sender_addr; li a1, 0; li a3, 0; li a4, 0; li a5, 0; li a6, " ++ toString (accountWriteHasNonce + accountWriteHasTouched) ++ "; jal ra, account_write_record\n" ++
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
  "  bnez a0, .Lbv_auth_prepare_fail\n" ++  -- was 40 → 72
  -- Auth-phase ExceptionalHalt (per-auth OOG): prepare returned a0=0 with
  -- runtime_tx_auth_phase_halted set. Publish failed receipt (gas_left=0,
  -- status=0) and rejoin the shared postlude — do NOT enter dispatch (would
  -- clear halted and run body). account_reads from asof before OOG stay.
  "  la t0, runtime_tx_auth_phase_halted; ld t1, 0(t0); bnez t1, .Lbv_mtx_auth_phase_oog\n" ++
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
  "  jal ra, account_state_delegation_code_resolve\n" ++
  -- #11163: empty-code (BAL hit or miss) enters the shared message processor
  -- the same way as contracts.  The depth-0 precompile arm inside
  -- `runtime_dispatcher_call` classifies after move_ether; inactive falls
  -- through to the bytecode loop (codeSize 0 → STOP).
  "  j .Lbv_mtx_is_contract\n" ++
  -- Inactive / non-precompile resume from the shared-body kernel tree.
  ".Lbv_mtx_precompile_not_active:\n" ++
  "  la t0, bv_mtx_precompile_lane; sd zero, 0(t0)\n" ++
  "  j .Lruntime_dispatcher_regular_loop\n" ++
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
  -- The current block-access index remains live for the map-builder/account-write
  -- seams below; it is no longer mirrored into a retired execution-log metadata
  -- array.
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
  -- `process_message` charges NEW_ACCOUNT before its snapshot when a nonzero
  -- top-level value transfer targets an account that is not alive
  -- (interpreter.py:285-288).  Reuse the direct-transfer predicate rather
  -- than reproducing its header, EIP-161, and BAL-overlay checks here.  This
  -- route owns the staging cell: `dispatch_tx_runtime_code` consumes it in
  -- the shared transaction gas fold and must not clear it on entry.
  "  la t0, runtime_tx_create_state_charge; sd zero, 0(t0)\n" ++
  topLevelValueRecipientStateGasAsm "bv_mtx_recipient_state" "bv_mtx_ctx" ++
  "  mv t1, t0; la t0, runtime_tx_create_state_charge; sd t1, 0(t0)\n" ++
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
  -- Preserve the auth-preparation outcome per transaction.  Receipt status is
  -- not sufficient: body REVERT keeps the authorization phase, while an
  -- auth/preparation OOG has status zero and must suppress its BAL effects.
  "  la t3, runtime_tx_post_preparation_reached; ld t5, 0(t3); la t3, bv_tx_auth_phase_applied_arr; add t3, t3, t0; sd t5, 0(t3)\n" ++
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
  -- Commit the just-successful transaction's current AccountState overlay before
  -- the next callable dispatch.  A failed receipt commits no code/existence
  -- mutations, exactly like its effect-log rollback above.
  -- Match `process_message`'s two snapshots: a successful body commits all
  -- pending AccountState; a failed body still commits the authorization phase
  -- iff the dispatcher reached the post-preparation coverage point.  A
  -- preparation OOG never reaches that point and therefore drops pending auth.
  -- r59nm: the storage_writes map commits on TX STATUS ALONE, decided here and
  -- NOT inside account_state_commit_pending.  The AccountState gate below also
  -- commits normally; only an authorization-phase halt restores the
  -- preparation snapshot.  The post-preparation marker is deliberately not
  -- used as a generic rollback trigger: unrelated early exits can occur before
  -- that point and must not truncate this transaction's pending state.  Merging
  -- storage on that disjunct promoted
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
  -- `clear_account_preserving_balance` / `destroy_account` converts the
  -- transaction's storage_writes for a deleted account into storage_reads
  -- (`state_tracker.py:556-579`) BEFORE `incorporate_tx_into_block` updates
  -- the BAL builder (`:855-858`).  Keep that ordering here: the guest's
  -- account-state commit helper also performs this conversion, but it is
  -- reached below the storage merge.  Running the idempotent conversion once
  -- while the tx map is still live prevents a deleted account's slot from
  -- being emitted as a spurious storage_change; the later call is a no-op for
  -- rows already removed and still owns the durable account commit.
  "  jal ra, account_state_promote_delete_reads\n" ++
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
  -- Auth-phase / prepare-prefix halt: drop auth-produced account_writes first.
  -- Finalize already restored AccountState pending to the pre-auth checkpoint
  -- (sender inclusion kept). Do not zero pending here — that dropped inclusion
  -- and forced a post-wipe reseed race. Auth OOG never enters the dispatcher, so
  -- seed upfront after the writes restore, then refund, then skip the success
  -- commit (coinbase + final commit_pending below still run).
  "  la t0, runtime_tx_auth_phase_halted; ld t2, 0(t0); bnez t2, .Lbv_mtx_preparation_rollback\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; ld t2, 0(t0); li t3, 1; bne t2, t3, .Lbv_mtx_refund_then_commit\n" ++
  ".Lbv_mtx_preparation_rollback:\n" ++
  "  la t0, account_writes_auth_prepare_mark; ld a0, 0(t0); jal ra, account_writes_restore_frame\n" ++
  "  la t0, account_state_pending_checkpoint; ld t1, 0(t0); la t0, account_state_pending_count; sd t1, 0(t0)\n" ++
  "  la t0, account_state_created_count; sd zero, 0(t0); la t0, account_state_delete_count; sd zero, 0(t0)\n" ++
  "  jal ra, dispatcher_seed_pending_upfront_sender_balance\n" ++
  ".Lbv_mtx_refund_then_commit:\n" ++
  blockVerdictMtxRecordSenderRefund ++
  "  la t0, runtime_tx_auth_phase_halted; ld t2, 0(t0); bnez t2, .Lbv_mtx_code_commit_done\n" ++
  "  la t0, runtime_tx_prepare_prefix_status; ld t2, 0(t0); li t3, 1; beq t2, t3, .Lbv_mtx_code_commit_done\n" ++
  ".Lbv_mtx_code_commit:\n" ++
  "  jal ra, account_state_commit_pending; bnez a0, .Lbv_mtx_bail\n" ++
  ".Lbv_mtx_code_commit_done:\n" ++
  "  la t0, evm_selfdestruct_destroyed_overflow; ld t1, 0(t0); bnez t1, .Lbv_mtx_bail\n" ++
  -- Spec stage: clear destroyed accounts before incorporate (fork.py:1201-1202).
  -- Apply destroyed-norm to the RAW nonstorage log here while the destroyed
  -- table is still live; next user tx wipes the table (mode=0) and block-end
  -- aggregate would otherwise miss CREATE+SD nonce phantoms (fc44).
  "  addi sp, sp, -16; sd ra, 0(sp); jal ra, nonstorage_apply_destroyed_norm; ld ra, 0(sp); addi sp, sp, 16\n" ++
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
  -- The block-storage incorporation above is complete; retain the existing
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
  -- The four checked request calls execute in this common post-user-loop phase.
  -- Each call captures its own execution rows and incorporates its own
  -- storage/read sets at N+1, so the old side-arena replay compensation is gone.
  "  jal ra, block_verdict_deferred_system_requests\n" ++
  "  bnez a0, .Lbv_requests_hash_fail\n" ++
  "  la t0, storage_writes_overflow; ld t1, 0(t0); bnez t1, .Lbv_fixed_arena_overflow_fail\n" ++
  -- One post-user path for every block (spec: one tx loop, then requests from
  -- logs). #11183 retired the deposit-capture-only shortcut that skipped the
  -- validation tail after root.
  "  j .Lbv_mtx_publish\n" ++
  ".Lbv_mtx_publish:\n" ++
  -- Terminal state-root replay.  `.Lbv_mtx_done` has already run every
  -- user/system read-set and write-set incorporation; no storage-map writer
  -- follows this label before validation and gas settlement.  The mode bit is
  -- therefore a placement fact, not a readiness guard: a zero map count means
  -- the block genuinely has no committed storage rows.
  "  li t0, 1; la t1, bsr_storage_from_map; sd t0, 0(t1)\n" ++
  "  la t0, bsr_root_p; ld a0, 0(t0); la t0, bsr_wit_p; ld a1, 0(t0); la t0, bsr_wl_v; ld a2, 0(t0)\n" ++
  "  la t0, bsr_wds_p; ld a3, 0(t0); la t0, bsr_wds_n; ld a4, 0(t0); la a5, sv_recomputed\n" ++
  "  la t0, bsr_ssz_p; ld a6, 0(t0); jal ra, block_state_root\n" ++
  "  mv s2, a0; la t0, bv_state_status; sd s2, 0(t0); bnez s2, .Lbv_state_fail\n" ++
  "  la t0, sv_recomputed; la t1, bsr_header_state_root_p; ld t1, 0(t1); li t2, 32\n" ++
  ".Lbv_terminal_root_cmp:\n" ++
  "  beqz t2, .Lbv_terminal_root_ok\n" ++
  "  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbv_cmp_mismatch\n" ++
  "  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_terminal_root_cmp\n" ++
  ".Lbv_terminal_root_ok:\n" ++
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
  -- A durable AccountState entry is a prior-tx live account and collides; a
  -- durable tombstone is a same-tx-created account already deleted at an
  -- earlier transaction boundary, so it deliberately falls through to the
  -- pre-block predicate (where it is absent and may be recreated).
  "  la a0, bv_create_addr; jal ra, account_state_lookup_current\n" ++
  "  beqz a0, .Lbv_mtx_creation_header_collision\n" ++
  "  li t0, 3; beq a0, t0, .Lbv_mtx_creation_header_collision\n" ++
  -- Only status 1 (an existing account with code) is an EIP-684 collision.
  -- Status 2 is an existing empty-code entry and is not a collision by
  -- itself; preserve the established fail-closed route until its CREATE
  -- preparation is modelled.  Sending status 2 through the collision
  -- settlement would reject valid creation fixtures whose target is merely
  -- represented by an empty code-state entry.
  "  li t0, 1; beq a0, t0, .Lbv_mtx_creation_collision\n" ++
  "  j .Lbv_mtx_creation_unsupported\n" ++
  ".Lbv_mtx_creation_header_collision:\n" ++
  "  ld a0, 8(s0); ld a1, 16(s0); la a2, bv_create_addr; ld a3, 80(s0); ld a4, 88(s0); jal ra, has_code_or_nonce_at_header_state_root\n" ++
  "  bnez a0, .Lbv_mtx_creation_collision\n" ++
  "  la t0, hcon_predicate; ld t0, 0(t0); bnez t0, .Lbv_mtx_creation_collision\n" ++
  "  j .Lbv_mtx_creation_prepare\n" ++
  -- A target absent from both current overlays and the authenticated header is
  -- the only non-collision case and continues into the CREATE preparation.
  -- Keep the collision arm separate so malformed access-list/runtime failures
  -- below retain their existing fail-closed route.
  ".Lbv_mtx_creation_collision:\n" ++
  -- `prepare_message` unconditionally adds the computed top-level CREATE
  -- target to accessed_addresses before collision handling (utils/message.py:
  -- 56-71).  Record that touch even though no initcode executes.
  "  la a0, bv_create_addr; jal ra, account_read_record\n" ++
  -- Collision is an exceptional transaction: all regular gas is consumed and
  -- the state-gas reservoir remains available (the same settlement as the
  -- single-tx collision branch). Publish the indexed result and rejoin the
  -- ordinary MTx postlude so read sets, nonce and receipts are incorporated.
  "  la t4, bv_mtx_ctx; ld t5, 40(t4); li t4, 16777216\n" ++
  "  bgeu t5, t4, .Lbv_mtx_creation_collision_have_reservoir\n" ++
  "  li t5, 0\n" ++
  "  j .Lbv_mtx_creation_collision_gas_ready\n" ++
  ".Lbv_mtx_creation_collision_have_reservoir:\n" ++
  "  sub t5, t5, t4\n" ++
  ".Lbv_mtx_creation_collision_gas_ready:\n" ++
  "  la t4, bv_runtime_gas_left; sd t5, 0(t4)\n" ++
  "  la t4, bv_runtime_refund_counter; sd zero, 0(t4)\n" ++
  "  la t4, bv_runtime_calldata_floor; sd zero, 0(t4)\n" ++
  "  la t4, bv_mtx_i; ld t1, 0(t4); slli t2, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t2; sd t5, 0(t3)\n" ++
  "  la t3, bv_mtx_refund; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t3, bv_mtx_calldata; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  li t4, 1; la t3, bv_tx_is_creation_arr; add t3, t3, t2; sd t4, 0(t3)\n" ++
  "  slli t2, t1, 4; la t3, bv_tx_log_window; add t3, t3, t2; la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3); la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  -- The collision path never enters the dispatcher, so it must consume the
  -- staged process_transaction gas debit itself before the shared settlement
  -- postlude reads the sender's live balance for the refund.
  "  jal ra, dispatcher_seed_pending_upfront_sender_balance\n" ++
  "  la t0, bv_mtx_i; ld a0, 0(t0); jal ra, dispatcher_capture_exec_state_gas\n" ++
  bvReceiptsShapeSet 5 true ++
  "  li a4, 0\n" ++
  -- The shared postlude keys the effective recipient from ctx+72.  A CREATE
  -- collision has no ordinary recipient, so expose the computed target there.
  "  la t0, bv_create_addr; la t1, bv_mtx_ctx; addi t1, t1, 72; li t2, 20\n" ++
  ".Lbv_mtx_creation_collision_key_copy:\n  beqz t2, .Lbv_mtx_creation_collision_effects; lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_mtx_creation_collision_key_copy\n" ++
  ".Lbv_mtx_creation_collision_effects:\n" ++
  "  j .Lbv_mtx_effects_kept\n" ++
  -- EIP-7702 set_delegation ExceptionalHalt (per-auth state-gas OOG). Prepare
  -- already rolled pending/effects and left halted=1 + a0=0. Publish a failed
  -- receipt with gas_left=0 and rejoin the shared postlude. Do NOT seed upfront
  -- here: finalize (halted) restores pending to the pre-auth checkpoint and
  -- would wipe a pre-finalize seed; effects_kept re-seeds after finalize.
  ".Lbv_mtx_auth_phase_oog:\n" ++
  "  la t4, bv_mtx_i; ld t1, 0(t4); slli t2, t1, 3\n" ++
  "  la t3, bv_mtx_gas_left; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t3, bv_mtx_refund; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t0, runtime_tx_calldata_floor; ld t5, 0(t0); la t3, bv_mtx_calldata; add t3, t3, t2; sd t5, 0(t3)\n" ++
  "  la t3, bv_tx_status_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t3, bv_tx_auth_phase_applied_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  la t3, bv_tx_is_creation_arr; add t3, t3, t2; sd zero, 0(t3)\n" ++
  "  slli t2, t1, 4; la t3, bv_tx_log_window; add t3, t3, t2; la t4, bv_last_log_start; ld t5, 0(t4); sd t5, 0(t3); la t4, bv_last_log_count; ld t5, 0(t4); sd t5, 8(t3)\n" ++
  "  la t0, bv_mtx_i; ld a0, 0(t0); jal ra, dispatcher_capture_exec_state_gas\n" ++
  bvReceiptsShapeSet 5 true ++
  "  j .Lbv_mtx_effects_kept\n" ++
  -- Fresh target: mirror the single CREATE prepare_dispatch charge.  A
  -- collision stays conservative until its error-receipt publication is also
  -- indexed; never run initcode for a target whose EIP-684 predicate is true.
  ".Lbv_mtx_creation_prepare:\n" ++
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
  -- the postlude's canonical block-storage preload.
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
  "  j .Lbv_after_tx_gas_precharge\n" ++
  blockVerdictMtxOogMaterialize

-- The N+1 system-request phase is pinned at the post-user-loop boundary.  The
-- universal MTx loop is now the sole live post-user-loop site; the former
-- single-transaction reconciliation definition was source-only dead and is
-- removed, so there is no sibling occurrence to duplicate.
#guard (blockVerdictMtxRuntimeLoop.splitOn
  "  jal ra, block_verdict_deferred_system_requests\n").length == 2

end EvmAsm.Codegen
