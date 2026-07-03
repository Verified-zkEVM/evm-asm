blsg_zero96:
  li t0, 12
.Lblsg_zero96_loop:
  sd zero, 0(a0)
  addi a0, a0, 8
  addi t0, t0, -1
  bnez t0, .Lblsg_zero96_loop
  ret
