bnp_fp2_eq:
  li t0, 8
.Lbnp_fp2_eq_loop:
  beqz t0, .Lbnp_fp2_eq_yes
  ld t1, 0(a0)
  ld t2, 0(a1)
  bne t1, t2, .Lbnp_fp2_eq_no
  addi a0, a0, 8
  addi a1, a1, 8
  addi t0, t0, -1
  j .Lbnp_fp2_eq_loop
.Lbnp_fp2_eq_yes:
  li a0, 1
  ret
.Lbnp_fp2_eq_no:
  li a0, 0
  ret
