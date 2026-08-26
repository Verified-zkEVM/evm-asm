bal_builder_append_balance:
  addi sp, sp, -40; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)
  jal ra, bal_builder_ensure_account; bltz a0, .Lbabb_overflow
  la t0, bal_builder_balance_count; ld t1, 0(t0); li t2, 105000; bgeu t1, t2, .Lbabb_overflow
  slli t2, t1, 6; la t3, bal_builder_balance_changes; add t3, t3, t2; ld t4, 8(sp); li t5, 20
.Lbabb_addr:
  beqz t5, .Lbabb_bai; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lbabb_addr
.Lbabb_bai:
  la t3, bal_builder_balance_changes; slli t2, t1, 6; add t3, t3, t2; ld t4, 16(sp); sd t4, 24(t3); ld t4, 24(sp); ld t5, 0(t4); sd t5, 32(t3); ld t5, 8(t4); sd t5, 40(t3); ld t5, 16(t4); sd t5, 48(t3); ld t5, 24(t4); sd t5, 56(t3); addi t1, t1, 1; la t0, bal_builder_balance_count; sd t1, 0(t0); li a0, 0; j .Lbabb_ret
.Lbabb_overflow:
  la t0, bal_builder_balance_overflow; li t1, 1; sd t1, 0(t0); la t0, bal_builder_overflow; sd t1, 0(t0); li a0, 1
.Lbabb_ret:
  ld ra, 0(sp); addi sp, sp, 40; ret
