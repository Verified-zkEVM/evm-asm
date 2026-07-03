blsg_subgroup_g1:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a2, a0
  la a0, blsg_n_be
  li a1, 32
  la a3, blsg_sub_out
  jal ra, blsg_scalar_mul
  ld ra, 0(sp)
  addi sp, sp, 16
  ret                            # scalar_mul already returns the inf flag
