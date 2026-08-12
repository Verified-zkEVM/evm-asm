account_writes_auth_current:
  addi sp, sp, -40; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); mv s0, a0; mv s1, a1; mv s2, a2; mv a0, s0; jal ra, account_read_record
  li s3, 0; la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawa_tx_loop:
  bgeu t3, t1, .Lawa_block_init; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawa_tx_cmp:
  beqz t6, .Lawa_tx_key; lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .Lawa_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawa_tx_cmp
.Lawa_tx_next:
  addi t3, t3, 1; j .Lawa_tx_loop
.Lawa_tx_key:
  ld t0, 112(t5); andi t1, t0, 2; beqz t1, .Lawa_tx_next; andi t1, t0, 8; beqz t1, .Lawa_tx_next; andi t1, t0, 16; beqz t1, .Lawa_tx_next; j .Lawa_hit
.Lawa_block_init:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawa_block_loop:
  bgeu t3, t1, .Lawa_miss; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawa_block_cmp:
  beqz t6, .Lawa_block_key; lbu a3, 0(a0); lbu a4, 0(a1); bne a3, a4, .Lawa_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawa_block_cmp
.Lawa_block_next:
  addi t3, t3, 1; j .Lawa_block_loop
.Lawa_block_key:
  ld t0, 112(t5); andi t1, t0, 2; beqz t1, .Lawa_block_next; andi t1, t0, 8; beqz t1, .Lawa_block_next; andi t1, t0, 16; beqz t1, .Lawa_block_next; j .Lawa_hit
.Lawa_hit:
  ld t1, 64(t5); sd t1, 0(s1); ld t1, 96(t5); sd t1, 0(s2); andi t1, t1, 2; bnez t1, .Lawa_live; li a0, 2; j .Lawa_ret
.Lawa_live:
  li a0, 1; j .Lawa_ret
.Lawa_miss:
  li a0, 0
.Lawa_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); addi sp, sp, 40; ret
