p256_pow:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                      # base
  mv s1, a1                      # exponent bytes
  mv s2, a2                      # output
  mv s6, a3                      # mul params
  la a0, p256_one_be
  la a1, p256_acc
  li a2, 32
  jal ra, p256_copy_n            # acc = 1
  li s3, 0                       # exponent byte index
.Lp256_pow_byte:
  li t0, 32
  bgeu s3, t0, .Lp256_pow_done
  add t0, s1, s3
  lbu s4, 0(t0)
  li s5, 128
.Lp256_pow_bit:
  beqz s5, .Lp256_pow_next
  la a0, p256_acc
  la a1, p256_acc
  la a2, p256_acc
  mv a3, s6
  jal ra, p256_op_with           # acc = acc^2
  and t0, s4, s5
  beqz t0, .Lp256_pow_skip
  la a0, p256_acc
  mv a1, s0
  la a2, p256_acc
  mv a3, s6
  jal ra, p256_op_with           # acc *= base
.Lp256_pow_skip:
  srli s5, s5, 1
  j .Lp256_pow_bit
.Lp256_pow_next:
  addi s3, s3, 1
  j .Lp256_pow_byte
.Lp256_pow_done:
  la a0, p256_acc
  mv a1, s2
  li a2, 32
  jal ra, p256_copy_n
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
