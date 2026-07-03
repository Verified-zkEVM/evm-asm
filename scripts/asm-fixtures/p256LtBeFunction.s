p256_lt_be:
  li t2, 32
  mv t0, a0
  mv t1, a1
.Lp256_lt_loop:
  beqz t2, .Lp256_lt_no          # equal => not less
  lbu t3, 0(t0)
  lbu t4, 0(t1)
  bltu t3, t4, .Lp256_lt_yes
  bltu t4, t3, .Lp256_lt_no
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lp256_lt_loop
.Lp256_lt_yes:
  li a0, 1
  ret
.Lp256_lt_no:
  li a0, 0
  ret
