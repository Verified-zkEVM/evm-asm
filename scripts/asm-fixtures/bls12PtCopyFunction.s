blq_pt_copy:
  li t2, 216
.Lblq_pt_copy_loop:
  ld t3, 0(a0)
  sd t3, 0(a1)
  addi a0, a0, 8
  addi a1, a1, 8
  addi t2, t2, -1
  bnez t2, .Lblq_pt_copy_loop
  ret
