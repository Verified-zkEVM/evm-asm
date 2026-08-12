account_writes_tombstone_balance_zero:
  addi sp, sp, -160; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); mv s0, a0; li s1, 0; li s2, 0
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawtbz_tx_loop:
  bgeu t3, t1, .Lawtbz_block_init; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawtbz_tx_cmp:
  beqz t6, .Lawtbz_tx_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawtbz_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawtbz_tx_cmp
.Lawtbz_tx_next:
  addi t3, t3, 1; j .Lawtbz_tx_loop
.Lawtbz_tx_hit:
  mv s1, t5
  j .Lawtbz_block_init
.Lawtbz_block_init:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawtbz_block_loop:
  bgeu t3, t1, .Lawtbz_state_select; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawtbz_block_cmp:
  beqz t6, .Lawtbz_block_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawtbz_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawtbz_block_cmp
.Lawtbz_block_next:
  addi t3, t3, 1; j .Lawtbz_block_loop
.Lawtbz_block_hit:
  mv s2, t5
.Lawtbz_state_select:
  beqz s1, .Lawtbz_use_block_state; ld t0, 112(s1); andi t1, t0, 8; bnez t1, .Lawtbz_use_tx_state
.Lawtbz_use_block_state:
  beqz s2, .Lawtbz_no; ld t0, 112(s2); andi t1, t0, 8; beqz t1, .Lawtbz_no; mv s3, s2; j .Lawtbz_state_check
.Lawtbz_use_tx_state:
  mv s3, s1
.Lawtbz_state_check:
  ld t0, 72(s3); beqz t0, .Lawtbz_yes; mv a0, s0; jal ra, account_state_created_contains; bnez a0, .Lawtbz_no
  ld t1, 112(s3); andi t2, t1, 4; beqz t2, .Lawtbz_components; ld t3, 88(s3); bnez t3, .Lawtbz_no
.Lawtbz_components:
  li s4, 0; li s5, 0
  beqz s1, .Lawtbz_block_components; ld t0, 112(s1); andi t1, t0, 1; beqz t1, .Lawtbz_tx_nonce; ld t2, 32(s1); sd t2, 128(sp); ld t2, 40(s1); sd t2, 136(sp); ld t2, 48(s1); sd t2, 144(sp); ld t2, 56(s1); sd t2, 152(sp); li s4, 1
.Lawtbz_tx_nonce:
  andi t1, t0, 2; beqz t1, .Lawtbz_block_components; ld t2, 64(s1); sd t2, 120(sp); li s5, 1
.Lawtbz_block_components:
  beqz s2, .Lawtbz_prestate_check; ld t0, 112(s2); bnez s4, .Lawtbz_block_nonce; andi t1, t0, 1; beqz t1, .Lawtbz_block_nonce; ld t2, 32(s2); sd t2, 128(sp); ld t2, 40(s2); sd t2, 136(sp); ld t2, 48(s2); sd t2, 144(sp); ld t2, 56(s2); sd t2, 152(sp); li s4, 1
.Lawtbz_block_nonce:
  bnez s5, .Lawtbz_prestate_check; andi t1, t0, 2; beqz t1, .Lawtbz_prestate_check; ld t2, 64(s2); sd t2, 120(sp); li s5, 1
.Lawtbz_prestate_check:
  bnez s4, .Lawtbz_need_nonce; j .Lawtbz_prestate
.Lawtbz_need_nonce:
  bnez s5, .Lawtbz_restore_direct; j .Lawtbz_prestate
.Lawtbz_prestate:
  sd zero, 80(sp); sd zero, 88(sp); sd zero, 96(sp); sd zero, 104(sp); sd zero, 112(sp); mv a0, s0; addi a1, sp, 80; la t0, sv_pre_rlp_ptr; ld a2, 0(t0); la t0, sv_pre_rlp_len; ld a3, 0(t0); la t0, bv_witness_state_ptr; ld a4, 0(t0); la t0, bv_witness_state_len; ld a5, 0(t0); jal ra, account_resolve_pre_state; bnez a0, .Lawtbz_no
.Lawtbz_restore_direct:
  beqz s4, .Lawtbz_restore_nonce; ld t0, 128(sp); sd t0, 88(sp); ld t0, 136(sp); sd t0, 96(sp); ld t0, 144(sp); sd t0, 104(sp); ld t0, 152(sp); sd t0, 112(sp)
.Lawtbz_restore_nonce:
  beqz s5, .Lawtbz_zero_check; ld t0, 120(sp); sd t0, 80(sp)
.Lawtbz_zero_check:
  ld t0, 80(sp); bnez t0, .Lawtbz_no; ld t0, 88(sp); ld t1, 96(sp); or t0, t0, t1; ld t1, 104(sp); or t0, t0, t1; ld t1, 112(sp); or t0, t0, t1; bnez t0, .Lawtbz_no; j .Lawtbz_yes
.Lawtbz_yes:
  li a0, 1; j .Lawtbz_ret
.Lawtbz_no:
  li a0, 0
.Lawtbz_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); addi sp, sp, 160; ret
