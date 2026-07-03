p256_point_add:
  addi sp, sp, -40
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  mv a0, s0
  mv a1, s1
  jal ra, p256_eq32
  beqz a0, .Lp256_add_distinct
  addi a0, s0, 32
  addi a1, s1, 32
  jal ra, p256_eq32
  beqz a0, .Lp256_add_inf       # x equal, y opposite: P + (-P)
  mv a0, s0
  mv a1, s2
  jal ra, p256_point_dbl        # x and y equal: P + P
  j .Lp256_add_ret
.Lp256_add_distinct:
  addi a0, s1, 32
  addi a1, s0, 32
  la a2, p256_lam
  la a3, p256_pb_sub_p
  jal ra, p256_op_with          # lam = y2 - y1
  mv a0, s1
  mv a1, s0
  la a2, p256_den
  la a3, p256_pb_sub_p
  jal ra, p256_op_with          # den = x2 - x1
  la a0, p256_den
  la a1, p256_pm2_be
  la a2, p256_inv_out
  la a3, p256_pb_mul_p
  jal ra, p256_pow              # inv_out = (x2 - x1)^-1
  la a0, p256_lam
  la a1, p256_inv_out
  la a2, p256_lam
  la a3, p256_pb_mul_p
  jal ra, p256_op_with          # lam = (y2-y1)/(x2-x1)
  mv a0, s0
  mv a1, s1
  mv a2, s2
  jal ra, p256_chord_tail
  li a0, 0
  j .Lp256_add_ret
.Lp256_add_inf:
  mv a0, s2
  li a1, 64
.Lp256_add_zero:
  sb zero, 0(a0)
  addi a0, a0, 1
  addi a1, a1, -1
  bnez a1, .Lp256_add_zero
  li a0, 1
.Lp256_add_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
