bal_builder_ensure_account:
  addi sp, sp, -48; sd s0, 0(sp); sd s1, 8(sp); sd s2, 16(sp); sd s3, 24(sp); sd s4, 32(sp); sd s5, 40(sp)
  mv s0, a0; la s1, bal_builder_account_count; ld s2, 0(s1); li s3, 0; la s4, bal_builder_accounts
.Lbabe_scan:
  bgeu s3, s2, .Lbabe_append
  slli s5, s3, 1; add s5, s5, s3; slli s5, s5, 3; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0
.Lbabe_cmp:
  beqz t0, .Lbabe_hit; lbu t3, 0(t1); lbu t4, 0(t2); bne t3, t4, .Lbabe_next; addi t1, t1, 1; addi t2, t2, 1; addi t0, t0, -1; j .Lbabe_cmp
.Lbabe_next:
  addi s3, s3, 1; j .Lbabe_scan
.Lbabe_append:
  li t0, 140000; bgeu s2, t0, .Lbabe_overflow
  slli s5, s2, 1; add s5, s5, s2; slli s5, s5, 3; add s5, s4, s5; li t0, 20; mv t1, s5; mv t2, s0
.Lbabe_copy:
  beqz t0, .Lbabe_append_done; lbu t3, 0(t2); sb t3, 0(t1); addi t1, t1, 1; addi t2, t2, 1; addi t0, t0, -1; j .Lbabe_copy
.Lbabe_append_done:
  addi t0, s2, 1; sd t0, 0(s1); mv s3, s2
.Lbabe_hit:
  mv a0, s3; j .Lbabe_ret
.Lbabe_overflow:
  la t0, bal_builder_overflow; li t1, 1; sd t1, 0(t0); li a0, -1
.Lbabe_ret:
  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp); addi sp, sp, 48; ret
