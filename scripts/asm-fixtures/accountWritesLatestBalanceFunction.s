account_writes_latest_balance:
  addi sp, sp, -32; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); mv s0, a0; mv s1, a1; mv a0, s0; jal ra, account_read_record
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawlb_tx_loop:
  bgeu t3, t1, .Lawlb_block_init; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawlb_tx_cmp:
  beqz t6, .Lawlb_tx_key; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawlb_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawlb_tx_cmp
.Lawlb_tx_next:
  addi t3, t3, 1; j .Lawlb_tx_loop
.Lawlb_tx_key:
  ld t0, 112(t5); andi t0, t0, 1; bnez t0, .Lawlb_hit; addi t3, t3, 1; j .Lawlb_tx_loop
.Lawlb_block_init:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawlb_block_loop:
  bgeu t3, t1, .Lawlb_miss; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawlb_block_cmp:
  beqz t6, .Lawlb_block_key; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawlb_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawlb_block_cmp
.Lawlb_block_next:
  addi t3, t3, 1; j .Lawlb_block_loop
.Lawlb_block_key:
  ld t0, 112(t5); andi t0, t0, 1; bnez t0, .Lawlb_hit; addi t3, t3, 1; j .Lawlb_block_loop
.Lawlb_hit:
  ld t0, 32(t5); sd t0, 0(s1); ld t0, 40(t5); sd t0, 8(s1); ld t0, 48(t5); sd t0, 16(s1); ld t0, 56(t5); sd t0, 24(s1); li a0, 1; j .Lawlb_ret
.Lawlb_miss:
  li a0, 0
.Lawlb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret
