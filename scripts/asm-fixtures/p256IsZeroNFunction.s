p256_is_zero_n:
  mv t1, a0
  mv t0, a1
.Lp256_iz_loop:
  beqz t0, .Lp256_iz_yes
  lbu t2, 0(t1)
  bnez t2, .Lp256_iz_no
  addi t1, t1, 1
  addi t0, t0, -1
  j .Lp256_iz_loop
.Lp256_iz_yes:
  li a0, 1
  ret
.Lp256_iz_no:
  li a0, 0
  ret
