secf_inv_mod_p:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  jal ra, secf_is_zero32
  beqz a0, .Lsecf_inv_nonzero
  mv a0, s1
  jal ra, secf_zero32
  li a0, 1
  j .Lsecf_inv_done
.Lsecf_inv_nonzero:
  la a0, secp256k1_p_minus_2_be
  addi a1, sp, 24
  jal ra, secf_copy32
  mv a0, s0
  addi a1, sp, 24
  mv a2, s1
  jal ra, secf_pow_mod_p
  li a0, 0
.Lsecf_inv_done:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  addi sp, sp, 64
  ret
