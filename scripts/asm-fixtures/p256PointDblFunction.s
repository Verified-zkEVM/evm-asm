p256_point_dbl:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  mv s1, a1
  addi a0, s0, 32
  li a1, 32
  jal ra, p256_is_zero_n
  beqz a0, .Lp256_dbl_finite
  mv a0, s1
  li t0, 8
.Lp256_dbl_zero:
  sb zero, 0(a0)
  sb zero, 1(a0)
  sb zero, 2(a0)
  sb zero, 3(a0)
  sb zero, 4(a0)
  sb zero, 5(a0)
  sb zero, 6(a0)
  sb zero, 7(a0)
  addi a0, a0, 8
  addi t0, t0, -1
  bnez t0, .Lp256_dbl_zero
  li a0, 1
  j .Lp256_dbl_ret
.Lp256_dbl_finite:
  mv a0, s0
  mv a1, s0
  la a2, p256_lam
  la a3, p256_pb_mul_p
  jal ra, p256_op_with           # lam = x^2
  la a0, p256_lam
  la a1, p256_lam
  la a2, p256_den
  la a3, p256_pb_add_p
  jal ra, p256_op_with           # den = 2x^2
  la a0, p256_den
  la a1, p256_lam
  la a2, p256_lam
  la a3, p256_pb_add_p
  jal ra, p256_op_with           # lam = 3x^2
  la a0, p256_lam
  la a1, p256_a_be
  la a2, p256_lam
  la a3, p256_pb_add_p
  jal ra, p256_op_with           # lam = 3x^2 + a
  addi a0, s0, 32
  addi a1, s0, 32
  la a2, p256_den
  la a3, p256_pb_add_p
  jal ra, p256_op_with           # den = 2y
  la a0, p256_den
  la a1, p256_pm2_be
  la a2, p256_inv_out
  la a3, p256_pb_mul_p
  jal ra, p256_pow               # inv_out = (2y)^-1
  la a0, p256_lam
  la a1, p256_inv_out
  la a2, p256_lam
  la a3, p256_pb_mul_p
  jal ra, p256_op_with           # lam = (3x^2 + a) / 2y
  mv a0, s0
  mv a1, s0
  mv a2, s1
  jal ra, p256_chord_tail
  li a0, 0
.Lp256_dbl_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
