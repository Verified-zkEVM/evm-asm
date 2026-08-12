account_writes_latest_nonce_block:
  addi sp, sp, -24; sd s0, 0(sp); sd s1, 8(sp); sd ra, 16(sp); mv s0, a0; mv s1, a1; mv a0, s0; jal ra, account_read_record
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lawlnb_loop:
  bgeu t3, t1, .Lawlnb_miss; slli t4, t3, 7; add t4, t2, t4; mv t5, t4; mv t6, s0; li a2, 20
.Lawlnb_cmp:
  beqz a2, .Lawlnb_key; lbu a3, 0(t5); lbu a4, 0(t6); bne a3, a4, .Lawlnb_next; addi t5, t5, 1; addi t6, t6, 1; addi a2, a2, -1; j .Lawlnb_cmp
.Lawlnb_next:
  addi t3, t3, 1; j .Lawlnb_loop
.Lawlnb_key:
  ld t0, 112(t4); andi t0, t0, 2; beqz t0, .Lawlnb_next; ld t0, 64(t4); sd t0, 0(s1); li a0, 1; j .Lawlnb_ret
.Lawlnb_miss:
  li a0, 0
.Lawlnb_ret:
  ld s0, 0(sp); ld s1, 8(sp); ld ra, 16(sp); addi sp, sp, 24; ret
