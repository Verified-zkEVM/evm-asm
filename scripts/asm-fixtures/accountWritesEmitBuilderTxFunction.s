account_writes_emit_builder_tx:
  addi sp, sp, -112
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  la t0, current_block_access_index; ld s7, 0(t0); la s0, tx_account_writes_count; ld s1, 0(s0); li s2, 0xbf780000; li s3, 0
.Laweb_loop:
  bgeu s3, s1, .Laweb_done; slli t0, s3, 7; add s4, s2, t0
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0; li s5, 0
.Laweb_scan:
  bgeu t3, t1, .Laweb_header; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s4
.Laweb_cmp:
  beqz t6, .Laweb_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Laweb_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Laweb_cmp
.Laweb_next:
  addi t3, t3, 1; j .Laweb_scan
.Laweb_hit:
  mv s5, t5; j .Laweb_header
.Laweb_header:
  bnez s5, .Laweb_parent
.Laweb_parent:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0); la t0, sv_pre_rlp_len; ld a1, 0(t0); mv a2, s4; li a3, 20; la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); la a6, account_builder_pre_account; jal ra, account_at_header_state_root; sd a0, 80(sp)
  mv a0, s4; la a1, account_builder_pre_account; la t0, sv_pre_rlp_ptr; ld a2, 0(t0); la t0, sv_pre_rlp_len; ld a3, 0(t0); la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); jal ra, account_resolve_pre_state
  ld s8, 112(s4)
  andi t0, s8, 1; bnez t0, .Laweb_balance_have; j .Laweb_nonce
.Laweb_balance_have:
  la t0, bald_bal_bit_set; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  la s6, account_builder_pre_account; addi s6, s6, 8
.Laweb_balance_cmp:
  ld t0, 0(s6); ld t1, 32(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 8(s6); ld t1, 40(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 16(s6); ld t1, 48(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 24(s6); ld t1, 56(s4); beq t0, t1, .Laweb_bal_eq
  li t0, 4; bgeu s3, t0, .Laweb_balance_trace_done; li t0, 96; mul t0, s3, t0; la t1, account_builder_diag_balance_pairs; add t1, t1, t0
  ld t0, 0(s4); sd t0, 0(t1); ld t0, 8(s4); sd t0, 8(t1); ld t0, 16(s4); sd t0, 16(t1); ld t0, 24(s4); sd t0, 24(t1)
  ld t0, 0(s6); sd t0, 32(t1); ld t0, 8(s6); sd t0, 40(t1); ld t0, 16(s6); sd t0, 48(t1); ld t0, 24(s6); sd t0, 56(t1)
  ld t0, 32(s4); sd t0, 64(t1); ld t0, 40(s4); sd t0, 72(t1); ld t0, 48(s4); sd t0, 80(t1); ld t0, 56(s4); sd t0, 88(t1)
.Laweb_balance_trace_done:
  ld t0, 0(s6); ld t1, 32(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 8(s6); ld t1, 40(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 16(s6); ld t1, 48(s4); bne t0, t1, .Laweb_balance_emit; ld t0, 24(s6); ld t1, 56(s4); beq t0, t1, .Laweb_nonce
.Laweb_balance_emit:
  la t0, bald_bal_differs; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  la t0, bald_bal_ne_bai_mask; ld t1, 0(t0); li t2, 1; sll t2, t2, s7; or t1, t1, t2; sd t1, 0(t0)
  mv a0, s4; mv a1, s7; addi a2, s4, 32; jal ra, bal_builder_append_balance
  j .Laweb_nonce
.Laweb_bal_eq:
  la t0, bald_bal_eq_bai_mask; ld t1, 0(t0); li t2, 1; sll t2, t2, s7; or t1, t1, t2; sd t1, 0(t0)
  ld t1, 0(s6); la t0, bald_bal_eq_val_lo; sd t1, 0(t0); ld t1, 24(s6); la t0, bald_bal_eq_val_hi; sd t1, 0(t0)
  ld t1, 0(s4); la t0, bald_bal_eq_addr_a; sd t1, 0(t0); ld t1, 8(s4); la t0, bald_bal_eq_addr_b; sd t1, 0(t0)
.Laweb_nonce:
  andi t0, s8, 2; bnez t0, .Laweb_nonce_have; j .Laweb_code
.Laweb_nonce_have:
  la t0, bald_non_bit_set; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  la t0, account_builder_pre_account; ld t0, 0(t0)
.Laweb_nonce_cmp:
  ld t1, 64(s4); beq t0, t1, .Laweb_non_eq; la t5, bald_non_differs; ld t6, 0(t5); addi t6, t6, 1; sd t6, 0(t5); la t5, bald_non_ne_bai_mask; ld t6, 0(t5); li t3, 1; sll t3, t3, s7; or t6, t6, t3; sd t6, 0(t5); mv a0, s4; mv a1, s7; mv a2, t1; jal ra, bal_builder_append_nonce
  j .Laweb_code
.Laweb_non_eq:
  la t2, bald_non_eq_bai_mask; ld t3, 0(t2); li t4, 1; sll t4, t4, s7; or t3, t3, t4; sd t3, 0(t2)
  la t2, bald_non_eq_val_pre; sd t0, 0(t2); la t2, bald_non_eq_val_post; sd t1, 0(t2)
  li t2, 4; bgeu s3, t2, .Laweb_nonce_trace_done; li t2, 48; mul t2, s3, t2; la t3, account_builder_diag_nonce_pairs; add t3, t3, t2
  ld t2, 0(s4); sd t2, 0(t3); ld t2, 8(s4); sd t2, 8(t3); ld t2, 16(s4); sd t2, 16(t3); ld t2, 24(s4); sd t2, 24(t3); sd t0, 32(t3); ld t2, 64(s4); sd t2, 40(t3)
.Laweb_nonce_trace_done:
  ld t1, 64(s4); beq t0, t1, .Laweb_code; mv a0, s4; mv a1, s7; mv a2, t1; jal ra, bal_builder_append_nonce
.Laweb_code:
  andi t0, s8, 4; bnez t0, .Laweb_code_have; j .Laweb_advance
.Laweb_code_have:
  ld a0, 80(s4); ld a1, 88(s4); la a2, account_builder_post_code_hash; jal ra, zkvm_keccak256
  beqz s5, .Laweb_code_header; ld t0, 112(s5); andi t0, t0, 4; beqz t0, .Laweb_code_header; ld a0, 80(s5); ld a1, 88(s5); la a2, account_builder_block_code_hash; jal ra, zkvm_keccak256; la s6, account_builder_block_code_hash; j .Laweb_code_cmp
.Laweb_code_header:
  ld t0, 80(sp); li t1, 1; beq t0, t1, .Laweb_code_absent; la s6, account_builder_pre_account; addi s6, s6, 72; j .Laweb_code_cmp
.Laweb_code_absent:
  la s6, chahsr_empty_code_hash
.Laweb_code_cmp:
  la t0, account_builder_post_code_hash; ld t1, 0(t0); ld t2, 0(s6); bne t1, t2, .Laweb_code_emit; ld t1, 8(t0); ld t2, 8(s6); bne t1, t2, .Laweb_code_emit; ld t1, 16(t0); ld t2, 16(s6); bne t1, t2, .Laweb_code_emit; ld t1, 24(t0); ld t2, 24(s6); beq t1, t2, .Laweb_advance
.Laweb_code_emit:
  mv a0, s4; mv a1, s7; ld a2, 80(s4); ld a3, 88(s4); jal ra, bal_builder_append_code
.Laweb_advance:
  addi s3, s3, 1; j .Laweb_loop
.Laweb_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 112; ret
