blsg2_copy192:
  addi sp, sp, -16
  sd ra, 0(sp)
  li a2, 24
  jal ra, blsf_copy_quads
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
