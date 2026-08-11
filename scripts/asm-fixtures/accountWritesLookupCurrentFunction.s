account_writes_lookup_current:
  addi sp, sp, -24; sd ra, 0(sp); sd s0, 8(sp); mv s0, a0
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawlc_tx_loop:
  bgeu t3, t1, .Lawlc_block_init; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawlc_tx_cmp:
  beqz t6, .Lawlc_tx_key; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawlc_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawlc_tx_cmp
.Lawlc_tx_next:
  addi t3, t3, 1; j .Lawlc_tx_loop
.Lawlc_tx_key:
  ld t0, 112(t5); andi t1, t0, 8; beqz t1, .Lawlc_tx_next; ld t1, 72(t5); beqz t1, .Lawlc_deleted; andi t1, t0, 16; beqz t1, .Lawlc_empty; ld t1, 96(t5); andi t1, t1, 2; beqz t1, .Lawlc_deleted; andi t1, t0, 4; beqz t1, .Lawlc_empty; ld a1, 80(t5); ld a2, 88(t5); beqz a2, .Lawlc_empty; li a0, 1; j .Lawlc_ret
.Lawlc_block_init:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawlc_block_loop:
  bgeu t3, t1, .Lawlc_absent; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawlc_block_cmp:
  beqz t6, .Lawlc_block_key; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawlc_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawlc_block_cmp
.Lawlc_block_next:
  addi t3, t3, 1; j .Lawlc_block_loop
.Lawlc_block_key:
  ld t0, 112(t5); andi t1, t0, 8; beqz t1, .Lawlc_block_next; ld t1, 72(t5); beqz t1, .Lawlc_deleted; andi t1, t0, 16; beqz t1, .Lawlc_empty; ld t1, 96(t5); andi t1, t1, 2; beqz t1, .Lawlc_deleted; andi t1, t0, 4; beqz t1, .Lawlc_empty; ld a1, 80(t5); ld a2, 88(t5); beqz a2, .Lawlc_empty; li a0, 1; j .Lawlc_ret
.Lawlc_empty:
  li a0, 2; li a1, 0; li a2, 0; j .Lawlc_ret
.Lawlc_deleted:
  li a0, 3; li a1, 0; li a2, 0; j .Lawlc_ret
.Lawlc_absent:
  li a0, 0; li a1, 0; li a2, 0
.Lawlc_ret:
  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 24; ret
