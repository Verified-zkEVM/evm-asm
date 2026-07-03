bnc_is_inf64:
  li t0, 64
  mv t1, a0
.Lbnc_isinf_loop:
  beqz t0, .Lbnc_isinf_yes
  lbu t2, 0(t1)
  bnez t2, .Lbnc_isinf_no
  addi t1, t1, 1
  addi t0, t0, -1
  j .Lbnc_isinf_loop
.Lbnc_isinf_yes:
  li a0, 1
  ret
.Lbnc_isinf_no:
  li a0, 0
  ret
