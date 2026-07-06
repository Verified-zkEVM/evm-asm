blsg_copy96:
  li t0, 12
.Lblsg_copy96_loop:
  ld t1, 0(a0)
  sd t1, 0(a1)
  addi a0, a0, 8
  addi a1, a1, 8
  addi t0, t0, -1
  bnez t0, .Lblsg_copy96_loop
  ret
