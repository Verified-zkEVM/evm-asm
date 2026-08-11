blsg2_point_dbl:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  addi a0, s0, 96
  li a1, 96
  jal ra, blsg_is_zero_n
  bnez a0, .Lblsg2_dbl_inf       # y = 0 (covers all-zero infinity)
  mv a0, s0
  la a1, blsg2_lam
  li a2, 12
  jal ra, blsf_copy_quads        # lam = x
  la a0, blsg2_lam
  mv a1, s0
  jal ra, blsg2_fp2_mul          # lam = x^2
  la a0, blsg2_lam
  la a1, blsg2_den
  li a2, 12
  jal ra, blsf_copy_quads        # den = x^2
  la a0, blsg2_lam
  la a1, blsg2_den
  jal ra, blsg2_fp2_add          # lam = 2x^2
  la a0, blsg2_lam
  la a1, blsg2_den
  jal ra, blsg2_fp2_add          # lam = 3x^2
  addi a0, s0, 96
  la a1, blsg2_den
  li a2, 12
  jal ra, blsf_copy_quads        # den = y
  la a0, blsg2_den
  addi a1, s0, 96
  jal ra, blsg2_fp2_add          # den = 2y
  la a0, blsg2_den
  la a1, blsg2_inv_out
  jal ra, blsg2_fp2_inv          # inv_out = (2y)^-1
  la a0, blsg2_lam
  la a1, blsg2_inv_out
  jal ra, blsg2_fp2_mul          # lam = 3x^2 / 2y
  mv a0, s0
  mv a1, s0
  mv a2, s1
  jal ra, blsg2_chord_tail
  li a0, 0
  j .Lblsg2_dbl_ret
.Lblsg2_dbl_inf:
  mv a0, s1
  jal ra, blsg2_zero192
  li a0, 1
.Lblsg2_dbl_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
