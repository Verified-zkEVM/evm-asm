secf_inv_mod_n:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  jal ra, secf_is_zero32
  beqz a0, .Lsecf_invn_nonzero
  mv a0, s1
  jal ra, secf_zero32
  li a0, 1
  j .Lsecf_invn_done
.Lsecf_invn_nonzero:
  la a0, secf_n_minus_2_be
  addi a1, sp, 24
  jal ra, secf_copy32
  mv a0, s0
  addi a1, sp, 24
  mv a2, s1
  jal ra, secf_pow_mod_n
  li a0, 0
.Lsecf_invn_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 64
  ret
