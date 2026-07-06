swd_minimal_copy:
  mv t0, a0                   # src cursor
  mv t1, a1                   # remaining
.Lswd_skip:
  beqz t1, .Lswd_emit         # all zero -> length 0
  lbu t2, 0(t0); bnez t2, .Lswd_emit
  addi t0, t0, 1; addi t1, t1, -1; j .Lswd_skip
.Lswd_emit:
  sd t1, 0(a3)                # out length = remaining
  mv t3, a2; li t4, 0
.Lswd_cp:
  beq t4, t1, .Lswd_cpd
  add t5, t0, t4; lbu t6, 0(t5); add t2, t3, t4; sb t6, 0(t2)
  addi t4, t4, 1; j .Lswd_cp
.Lswd_cpd:
  ret
