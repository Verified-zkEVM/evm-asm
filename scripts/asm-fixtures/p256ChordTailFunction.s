p256_chord_tail:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la a0, p256_lam
  la a1, p256_lam
  la a2, p256_t1
  la a3, p256_pb_mul_p
  jal ra, p256_op_with           # t1 = lam^2
  la a0, p256_t1
  mv a1, s0
  la a2, p256_t1
  la a3, p256_pb_sub_p
  jal ra, p256_op_with           # t1 -= x1
  la a0, p256_t1
  mv a1, s1
  la a2, p256_t1
  la a3, p256_pb_sub_p
  jal ra, p256_op_with           # t1 -= x2  (t1 = x3)
  mv a0, s0
  la a1, p256_t1
  la a2, p256_t2
  la a3, p256_pb_sub_p
  jal ra, p256_op_with           # t2 = x1 - x3
  la a0, p256_t2
  la a1, p256_lam
  la a2, p256_t2
  la a3, p256_pb_mul_p
  jal ra, p256_op_with           # t2 *= lam
  la a0, p256_t2
  addi a1, s0, 32
  la a2, p256_t2
  la a3, p256_pb_sub_p
  jal ra, p256_op_with           # t2 -= y1  (t2 = y3)
  la a0, p256_t1
  mv a1, s2
  li a2, 32
  jal ra, p256_copy_n
  la a0, p256_t2
  addi a1, s2, 32
  li a2, 32
  jal ra, p256_copy_n
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
