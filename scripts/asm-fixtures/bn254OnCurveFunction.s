bnc_on_curve:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  mv a1, s0
  la a2, bnc_t
  jal ra, bnf_mul_mod_p         # t = x^2
  la a0, bnc_t
  mv a1, s0
  la a2, bnc_t
  jal ra, bnf_mul_mod_p         # t = x^3
  la a0, bnc_t
  la a1, bnf_b_be
  la a2, bnc_rhs
  jal ra, bnf_add_mod_p         # rhs = x^3 + 3
  addi a0, s0, 32
  addi a1, s0, 32
  la a2, bnc_y2
  jal ra, bnf_mul_mod_p         # y2 = y^2
  la a0, bnc_rhs
  la a1, bnc_y2
  jal ra, bnf_eq32
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 16
  ret
