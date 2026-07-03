bnc_zero64:
  li t0, 64
.Lbnc_zero64_loop:
  beqz t0, .Lbnc_zero64_ret
  sb zero, 0(a0)
  addi a0, a0, 1
  addi t0, t0, -1
  j .Lbnc_zero64_loop
.Lbnc_zero64_ret:
  ret
