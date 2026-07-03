bnp_fp2_is_zero:
  li t0, 8
  li t1, 0
.Lbnp_fp2_isz_loop:
  beqz t0, .Lbnp_fp2_isz_done
  ld t2, 0(a0)
  or t1, t1, t2
  addi a0, a0, 8
  addi t0, t0, -1
  j .Lbnp_fp2_isz_loop
.Lbnp_fp2_isz_done:
  seqz a0, t1
  ret
