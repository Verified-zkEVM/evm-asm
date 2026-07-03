p256_scalar_mul:
  addi sp, sp, -72
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                      # scalar bytes
  mv s1, a1                      # base point
  mv s2, a2                      # accumulator/output
  mv a0, s2
  li t0, 64
.Lp256_mul_zero:
  sb zero, 0(a0)
  addi a0, a0, 1
  addi t0, t0, -1
  bnez t0, .Lp256_mul_zero
  li s3, 1                       # accumulator is infinity
  li s4, 0                       # byte index
.Lp256_mul_byte:
  li t0, 32
  bgeu s4, t0, .Lp256_mul_done
  add t0, s0, s4
  lbu s5, 0(t0)
  li s6, 128
.Lp256_mul_bit:
  beqz s6, .Lp256_mul_next
  bnez s3, .Lp256_mul_skip_dbl
  mv a0, s2
  mv a1, s2
  jal ra, p256_point_dbl         # alias-safe in-place double
  mv s3, a0
.Lp256_mul_skip_dbl:
  and t0, s5, s6
  beqz t0, .Lp256_mul_adv
  beqz s3, .Lp256_mul_add
  mv a0, s1
  mv a1, s2
  li a2, 64
  jal ra, p256_copy_n
  li s3, 0
  j .Lp256_mul_adv
.Lp256_mul_add:
  mv a0, s2
  mv a1, s1
  la a2, p256_ptmp
  jal ra, p256_point_add
  mv s3, a0
  la a0, p256_ptmp
  mv a1, s2
  li a2, 64
  jal ra, p256_copy_n
.Lp256_mul_adv:
  srli s6, s6, 1
  j .Lp256_mul_bit
.Lp256_mul_next:
  addi s4, s4, 1
  j .Lp256_mul_byte
.Lp256_mul_done:
  mv a0, s3
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 72
  ret
