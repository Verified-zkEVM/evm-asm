blsg_is_zero_n:
  mv t1, a0
  mv t0, a1
.Lblsg_iz_loop:
  beqz t0, .Lblsg_iz_yes
  lbu t2, 0(t1)
  bnez t2, .Lblsg_iz_no
  addi t1, t1, 1
  addi t0, t0, -1
  j .Lblsg_iz_loop
.Lblsg_iz_yes:
  li a0, 1
  ret
.Lblsg_iz_no:
  li a0, 0
  ret
