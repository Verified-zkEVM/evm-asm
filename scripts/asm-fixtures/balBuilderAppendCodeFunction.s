bal_builder_append_code:
  addi sp, sp, -48; sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp); sd a3, 32(sp)
  jal ra, bal_builder_ensure_account; bltz a0, .Lbabcod_overflow
  la t0, bal_builder_code_count; ld t1, 0(t0); li t2, 13125; bgeu t1, t2, .Lbabcod_overflow
  slli t2, t1, 6; la t3, bal_builder_code_changes; add t3, t3, t2; ld t4, 8(sp); li t5, 20
.Lbabcod_addr:
  beqz t5, .Lbabcod_bai; lbu t6, 0(t4); sb t6, 0(t3); addi t4, t4, 1; addi t3, t3, 1; addi t5, t5, -1; j .Lbabcod_addr
.Lbabcod_bai:
  la t3, bal_builder_code_changes; slli t2, t1, 6; add t3, t3, t2; ld t4, 16(sp); sd t4, 24(t3); ld t4, 24(sp); sd t4, 32(t3); ld t4, 32(sp); sd t4, 40(t3); addi t1, t1, 1; la t0, bal_builder_code_count; sd t1, 0(t0); li a0, 0; j .Lbabcod_ret
.Lbabcod_overflow:
  la t0, bal_builder_code_overflow; li t1, 1; sd t1, 0(t0); la t0, bal_builder_overflow; sd t1, 0(t0); li a0, 1
.Lbabcod_ret:
  ld ra, 0(sp); addi sp, sp, 48; ret
