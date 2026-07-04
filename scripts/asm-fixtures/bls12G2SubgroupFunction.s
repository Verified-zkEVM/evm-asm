blsg2_subgroup_g2:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a2, a0
  la a0, blsg_n_be
  li a1, 32
  la a3, blsg2_sub_out
  jal ra, blsg2_scalar_mul
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
