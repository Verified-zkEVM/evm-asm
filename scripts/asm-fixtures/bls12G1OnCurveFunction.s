blsg_on_curve:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  mv a1, s0
  la a2, blsg_t
  jal ra, blsg_mul_mod_p         # t = x^2
  la a0, blsg_t
  mv a1, s0
  la a2, blsg_t
  jal ra, blsg_mul_mod_p         # t = x^3
  la a0, blsg_t
  la a1, blsg_b_be
  la a2, blsg_rhs
  jal ra, blsg_add_mod_p         # rhs = x^3 + 4
  addi a0, s0, 48
  addi a1, s0, 48
  la a2, blsg_y2
  jal ra, blsg_mul_mod_p         # y2 = y^2
  la a0, blsg_rhs
  la a1, blsg_y2
  jal ra, blsg_eq48
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 16
  ret
