blsg2_chord_tail:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la a0, blsg2_lam
  la a1, blsg2_t1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsg2_t1
  la a1, blsg2_lam
  jal ra, blsg2_fp2_mul          # t1 = lam^2
  la a0, blsg2_t1
  mv a1, s0
  jal ra, blsg2_fp2_sub          # t1 -= x1
  la a0, blsg2_t1
  mv a1, s1
  jal ra, blsg2_fp2_sub          # t1 -= x2  (t1 = x3)
  mv a0, s0
  la a1, blsg2_t2
  li a2, 12
  jal ra, blsf_copy_quads        # t2 = x1
  la a0, blsg2_t2
  la a1, blsg2_t1
  jal ra, blsg2_fp2_sub          # t2 = x1 - x3
  la a0, blsg2_t2
  la a1, blsg2_lam
  jal ra, blsg2_fp2_mul          # t2 *= lam
  la a0, blsg2_t2
  addi a1, s0, 96
  jal ra, blsg2_fp2_sub          # t2 -= y1  (t2 = y3)
  la a0, blsg2_t1
  mv a1, s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blsg2_t2
  addi a1, s2, 96
  li a2, 12
  jal ra, blsf_copy_quads
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
