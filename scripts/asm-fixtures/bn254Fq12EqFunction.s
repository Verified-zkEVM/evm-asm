bnq_eq:
  li t0, 48
.Lbnq_eq_loop:
  beqz t0, .Lbnq_eq_yes
  ld t1, 0(a0)
  ld t2, 0(a1)
  bne t1, t2, .Lbnq_eq_no
  addi a0, a0, 8
  addi a1, a1, 8
  addi t0, t0, -1
  j .Lbnq_eq_loop
.Lbnq_eq_yes:
  li a0, 1
  ret
.Lbnq_eq_no:
  li a0, 0
  ret
