/-
  EvmAsm.Codegen.Programs.BlockVerdictDepositFallback

  Direct EOA -> deposit-contract fallback for EIP-6110 request derivation.
  This is used only when runtime log capture produced no deposit logs; it derives
  canonical deposit requests directly from transaction calldata/value so the
  requests_hash check still compares execution-derived bytes.
-/

import EvmAsm.Codegen.Programs.BlockVerdictParams

namespace EvmAsm.Codegen

/-- Return one exactly when every transaction is a canonical direct call to the
    EIP-6110 deposit contract. This narrow predicate admits sequential runtime
    dispatch for log capture when the general independence test reports the
    expected same-recipient interaction. -/
def blockVerdictAllDirectDepositTxsFunction : String :=
  "block_verdict_all_direct_deposit_txs:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  li s0, 0; la t0, bv_tx_count; ld s1, 0(t0)\n" ++
  ".Lbvadt_loop:\n" ++
  "  beq s0, s1, .Lbvadt_yes\n" ++
  "  la a0, bv_mtx_skip_ctx; mv a1, s0; jal ra, multi_tx_nth_context\n" ++
  "  la t0, bv_mtx_skip_ctx\n" ++
  "  ld t1, 0(t0); bnez t1, .Lbvadt_no\n" ++
  "  ld t1, 48(t0); bnez t1, .Lbvadt_no\n" ++
  "  ld t1, 64(t0); li t2, 404; bne t1, t2, .Lbvadt_no\n" ++
  "  addi t1, t0, 72; la t2, pdr_deposit_addr; li t3, 20\n" ++
  ".Lbvadt_addr_cmp:\n" ++
  "  beqz t3, .Lbvadt_selector\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbvadt_no\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadt_addr_cmp\n" ++
  ".Lbvadt_selector:\n" ++
  "  ld t0, 56(t0)\n" ++
  "  lbu t1, 0(t0); li t2, 0x22; bne t1, t2, .Lbvadt_no\n" ++
  "  lbu t1, 1(t0); li t2, 0x89; bne t1, t2, .Lbvadt_no\n" ++
  "  lbu t1, 2(t0); li t2, 0x51; bne t1, t2, .Lbvadt_no\n" ++
  "  lbu t1, 3(t0); li t2, 0x18; bne t1, t2, .Lbvadt_no\n" ++
  "  addi s0, s0, 1; j .Lbvadt_loop\n" ++
  ".Lbvadt_yes:\n" ++
  "  li a0, 1; j .Lbvadt_ret\n" ++
  ".Lbvadt_no:\n" ++
  "  li a0, 0\n" ++
  ".Lbvadt_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32\n" ++
  "  ret\n"

/-- Try to append one canonical direct EOA deposit transaction.
    a0 = 192-byte tx context, a1 = output cursor, a2 = deposit index.
    Returns a0 = 1 and a1 = cursor+192 on append, otherwise a0 = 0 and a1 unchanged. -/
def blockVerdictAppendDirectDepositFunction : String :=
  "block_verdict_append_direct_deposit:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0; mv s2, a1; mv s3, a2\n" ++
  "  ld t1, 0(s0); bnez t1, .Lbvadd_no\n" ++
  "  ld t1, 48(s0); bnez t1, .Lbvadd_no\n" ++
  "  ld t1, 64(s0); li t2, 404; bne t1, t2, .Lbvadd_no\n" ++
  "  addi t1, s0, 72; la t2, pdr_deposit_addr; li t3, 20\n" ++
  ".Lbvadd_addr_cmp:\n" ++
  "  beqz t3, .Lbvadd_addr_ok\n" ++
  "  lbu t4, 0(t1); lbu t5, 0(t2); bne t4, t5, .Lbvadd_no\n" ++
  "  addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadd_addr_cmp\n" ++
  ".Lbvadd_addr_ok:\n" ++
  "  ld s1, 56(s0)\n" ++
  "  lbu t1, 0(s1); li t2, 0x22; bne t1, t2, .Lbvadd_no\n" ++
  "  lbu t1, 1(s1); li t2, 0x89; bne t1, t2, .Lbvadd_no\n" ++
  "  lbu t1, 2(s1); li t2, 0x51; bne t1, t2, .Lbvadd_no\n" ++
  "  lbu t1, 3(s1); li t2, 0x18; bne t1, t2, .Lbvadd_no\n" ++
  "  addi a0, s1, 4; li a1, 128; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s1, 36; li a1, 208; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s1, 68; li a1, 272; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s1, 132; li a1, 48; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s1, 212; li a1, 32; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s1, 276; li a1, 96; jal ra, edd_be32_eq; beqz a0, .Lbvadd_no\n" ++
  "  addi a0, s0, 96; li a1, 1000000000; la a2, c1_er_assembled\n" ++
  "  jal ra, u256_div_u64_be; bnez a0, .Lbvadd_no\n" ++
  "  la t0, c1_er_assembled; li t1, 0\n" ++
  ".Lbvadd_q_hi_zero:\n" ++
  "  li t2, 24; beq t1, t2, .Lbvadd_q_hi_ok\n" ++
  "  add t3, t0, t1; lbu t4, 0(t3); bnez t4, .Lbvadd_no\n" ++
  "  addi t1, t1, 1; j .Lbvadd_q_hi_zero\n" ++
  ".Lbvadd_q_hi_ok:\n" ++
  "  lbu t1, 24(t0); slli t1, t1, 56; lbu t2, 25(t0); slli t2, t2, 48; or t1, t1, t2\n" ++
  "  lbu t2, 26(t0); slli t2, t2, 40; or t1, t1, t2; lbu t2, 27(t0); slli t2, t2, 32; or t1, t1, t2\n" ++
  "  lbu t2, 28(t0); slli t2, t2, 24; or t1, t1, t2; lbu t2, 29(t0); slli t2, t2, 16; or t1, t1, t2\n" ++
  "  lbu t2, 30(t0); slli t2, t2, 8; or t1, t1, t2; lbu t2, 31(t0); or t1, t1, t2\n" ++
  "  li t2, 1000000000; bltu t1, t2, .Lbvadd_no\n" ++
  "  addi t1, s1, 164; mv t2, s2; li t3, 48\n" ++
  ".Lbvadd_copy_pubkey:\n" ++
  "  beqz t3, .Lbvadd_copy_pubkey_done\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadd_copy_pubkey\n" ++
  ".Lbvadd_copy_pubkey_done:\n" ++
  "  addi t1, s1, 244; addi t2, s2, 48; li t3, 32\n" ++
  ".Lbvadd_copy_wc:\n" ++
  "  beqz t3, .Lbvadd_copy_wc_done\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadd_copy_wc\n" ++
  ".Lbvadd_copy_wc_done:\n" ++
  "  la t1, c1_er_assembled; addi t1, t1, 31; addi t2, s2, 80; li t3, 8\n" ++
  ".Lbvadd_copy_amount:\n" ++
  "  beqz t3, .Lbvadd_copy_amount_done\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, -1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadd_copy_amount\n" ++
  ".Lbvadd_copy_amount_done:\n" ++
  "  addi t1, s1, 308; addi t2, s2, 88; li t3, 96\n" ++
  ".Lbvadd_copy_sig:\n" ++
  "  beqz t3, .Lbvadd_copy_sig_done\n" ++
  "  lbu t4, 0(t1); sb t4, 0(t2); addi t1, t1, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lbvadd_copy_sig\n" ++
  ".Lbvadd_copy_sig_done:\n" ++
  "  sd s3, 184(s2)\n" ++
  "  addi a1, s2, 192; li a0, 1; j .Lbvadd_ret\n" ++
  ".Lbvadd_no:\n" ++
  "  mv a1, s2; li a0, 0\n" ++
  ".Lbvadd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret\n"

/-- Derive direct EOA deposit requests from every transaction context in order. -/
def blockVerdictDirectDepositFallback : String :=
  "  la t0, c1_dlen; sd zero, 0(t0)\n" ++
  "  la t0, c1_dstatus; sd zero, 0(t0)\n" ++
  "  la s2, c1_dbody\n" ++
  "  li s3, 0\n" ++
  "  la t0, svf_tx_count; ld s4, 0(t0)\n" ++
  "  li s5, 0\n" ++
  ".Lbv_deposit_direct_loop:\n" ++
  "  beq s3, s4, .Lbv_deposit_direct_done\n" ++
  "  la a0, bv_mtx_skip_ctx; mv a1, s3; jal ra, multi_tx_nth_context\n" ++
  -- Direct request derivation is a fallback for missing runtime deposit logs,
  -- not an independent transaction executor.  A reverted transaction can
  -- retain the canonical calldata shape while its receipt status is zero;
  -- execution-specs derives EIP-6110 requests from successful receipt logs,
  -- so do not synthesize a request for that transaction.
  "  slli t0, s3, 3; la t1, bv_tx_status_arr; add t1, t1, t0; ld t1, 0(t1); beqz t1, .Lbv_deposit_direct_noappend\n" ++
  "  la a0, bv_mtx_skip_ctx; mv a1, s2; mv a2, s5; jal ra, block_verdict_append_direct_deposit\n" ++
  "  mv s2, a1\n" ++
  "  beqz a0, .Lbv_deposit_direct_noappend\n" ++
  "  addi s5, s5, 1\n" ++
  ".Lbv_deposit_direct_noappend:\n" ++
  "  addi s3, s3, 1; j .Lbv_deposit_direct_loop\n" ++
  ".Lbv_deposit_direct_done:\n" ++
  "  la t0, c1_dbody; sub t1, s2, t0; la t2, c1_dlen; sd t1, 0(t2)\n" ++
  "  bnez t1, .Lbv_deposit_body_ready\n"

end EvmAsm.Codegen
