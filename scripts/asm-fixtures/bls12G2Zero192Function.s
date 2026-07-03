blsg2_zero192:
  li t0, 24
.Lblsg2_z192:
  sd zero, 0(a0)
  addi a0, a0, 8
  addi t0, t0, -1
  bnez t0, .Lblsg2_z192
  ret
