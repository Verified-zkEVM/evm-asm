blsg_eq48:
  li t0, 48
  mv t1, a0
  mv t2, a1
.Lblsg_eq_loop:
  beqz t0, .Lblsg_eq_yes
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bne t3, t4, .Lblsg_eq_no
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  j .Lblsg_eq_loop
.Lblsg_eq_yes:
  li a0, 1
  ret
.Lblsg_eq_no:
  li a0, 0
  ret
