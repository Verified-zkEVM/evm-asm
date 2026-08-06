/- EIP-4895 body credits as authenticated non-storage effects. -/
namespace EvmAsm.Codegen

def blockVerdictWithdrawalNonstorageEffectsFunction : String := r#"
block_verdict_withdrawal_nonstorage_effects:
  addi sp, sp, -72
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  la t0, svf_wds_count; ld s0, 0(t0); la t0, svf_wds_ptr; ld s1, 0(t0); li s2, 0
  # ExecutionPayload.withdrawals is SSZ List[Withdrawal, 16].  This helper is
  # also reached from the direct-EOA reconciliation path, so enforce the
  # decode bound before using the count as a raw loop bound.
  li t0, 17; bgeu s0, t0, .Lbv_wdne_fail
.Lbv_wdne_loop:
  beq s2, s0, .Lbv_wdne_ok
  li t0, 44; mul t0, s2, t0; add s3, s1, t0
  # `process_withdrawals` calls create_ether for every descriptor, including a
  # zero amount.  Copy and record the recipient before the zero-delta branch:
  # zero suppresses the balance mutation, not the tracked get_account access.
  la s4, bv_wdne_addr; sd zero, 0(s4); sd zero, 8(s4); sd zero, 16(s4); sd zero, 24(s4)
  addi t0, s3, 16; mv t1, s4; li t2, 20
.Lbv_wdne_addr_copy:
  beqz t2, .Lbv_wdne_addr_done
  lbu t3, 0(t0); sb t3, 0(t1); addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbv_wdne_addr_copy
.Lbv_wdne_addr_done:
  addi t0, s3, 36; li t1, 8; li t2, 0
.Lbv_wdne_amount_or:
  beqz t1, .Lbv_wdne_amount_done
  lbu t3, 0(t0); or t2, t2, t3; addi t0, t0, 1; addi t1, t1, -1; j .Lbv_wdne_amount_or
.Lbv_wdne_amount_done:
  # `process_withdrawals` creates one TransactionState for the descriptor
  # list and `create_ether` performs `get_account` for every descriptor,
  # including a zero amount.  Record the recipient before the amount guard;
  # the nonzero path below resolves its pre-state balance separately.
  la a0, bv_wdne_addr; jal ra, account_read_record
  beqz t2, .Lbv_wdne_zero_amount
  la a0, bv_wdne_addr; la a1, bv_wdne_acct; la t0, sv_pre_rlp_ptr; ld a2, 0(t0); la t0, sv_pre_rlp_len; ld a3, 0(t0)
  la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); jal ra, account_resolve_pre_state
  bnez a0, .Lbv_wdne_fail
.Lbv_wdne_have_base:
  # `process_withdrawals` reuses one TransactionState for the whole descriptor
  # list.  On a repeated recipient, the next create_ether reads the preceding
  # withdrawal's post-balance, not the parent-state balance resolved above.
  # The effect log is that live transaction state; leave bv_wdne_acct+8 as the
  # pre-state fallback when no earlier record for this address exists.
  la a0, bv_wdne_addr; la a1, bv_wdne_acct; addi a1, a1, 8; jal ra, nonstorage_effect_latest_balance
  la t0, bsw_amount; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)
  addi a0, s3, 36; li a1, 8; la a2, bsw_amount; addi a2, a2, 24; jal ra, swr_rev_le_be
  la a0, bsw_amount; li a1, 1000000000; la a2, bsw_wei; jal ra, u256_mul_u64_be; bnez a0, .Lbv_wdne_fail
  la a0, bv_wdne_acct; addi a0, a0, 8; la a1, bsw_wei; la a2, bv_wdne_post; jal ra, u256_add_be; bnez a0, .Lbv_wdne_fail
  la t0, bv_wdne_acct; ld a3, 0(t0); mv a4, a3; la a0, bv_wdne_addr; la a1, bv_wdne_acct; addi a1, a1, 8; la a2, bv_wdne_post; jal ra, record_nonstorage_effect; bnez a0, .Lbv_wdne_fail
  j .Lbv_wdne_next
.Lbv_wdne_zero_amount:
  # The recipient read was recorded before the zero-delta guard.
.Lbv_wdne_next:
  addi s2, s2, 1; j .Lbv_wdne_loop
.Lbv_wdne_ok:
  li a0, 0; j .Lbv_wdne_ret
.Lbv_wdne_fail:
  li a0, 1
.Lbv_wdne_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); addi sp, sp, 72; ret
"#

end EvmAsm.Codegen
