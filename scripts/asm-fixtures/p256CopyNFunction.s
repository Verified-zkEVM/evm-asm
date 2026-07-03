p256_copy_n:
.Lp256_cpn_loop:
  beqz a2, .Lp256_cpn_done
  lbu t0, 0(a0)
  sb t0, 0(a1)
  addi a0, a0, 1
  addi a1, a1, 1
  addi a2, a2, -1
  j .Lp256_cpn_loop
.Lp256_cpn_done:
  ret
