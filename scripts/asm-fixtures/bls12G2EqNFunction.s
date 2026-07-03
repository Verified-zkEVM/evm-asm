blsg2_eq_n:
  mv t1, a0
  mv t2, a1
  mv t0, a2
.Lblsg2_eqn_loop:
  beqz t0, .Lblsg2_eqn_yes
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bne t3, t4, .Lblsg2_eqn_no
  addi t1, t1, 1
  addi t2, t2, 1
  addi t0, t0, -1
  j .Lblsg2_eqn_loop
.Lblsg2_eqn_yes:
  li a0, 1
  ret
.Lblsg2_eqn_no:
  li a0, 0
  ret
