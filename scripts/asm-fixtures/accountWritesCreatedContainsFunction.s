account_writes_created_contains:
  addi sp, sp, -16; sd ra, 0(sp); sd s0, 8(sp); mv s0, a0; la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lawc_loop:
  bgeu t3, t1, .Lawc_no; slli t4, t3, 7; add t5, t2, t4; mv a0, t5; mv a1, s0; li t6, 20
.Lawc_cmp:
  beqz t6, .Lawc_key; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lawc_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lawc_cmp
.Lawc_next:
  addi t3, t3, 1; j .Lawc_loop
.Lawc_key:
  ld t0, 112(t5); andi t1, t0, 16; beqz t1, .Lawc_next; ld t1, 96(t5); andi t1, t1, 8; bnez t1, .Lawc_yes; j .Lawc_next
.Lawc_yes:
  li a0, 1; j .Lawc_ret
.Lawc_no:
  li a0, 0
.Lawc_ret:
  ld ra, 0(sp); ld s0, 8(sp); addi sp, sp, 16; ret
