secp256k1_scalar_mul:
  addi sp, sp, -72
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                      # scalar bytes
  mv s1, a1                      # base point
  mv s2, a2                      # accumulator/output
  mv a0, s2
  jal ra, secp256k1_point_zero64
  li s3, 1                       # accumulator is infinity
  li s4, 0                       # byte index
.Lsecc_mul_byte_loop:
  li t0, 32
  bgeu s4, t0, .Lsecc_mul_done
  add t0, s0, s4
  lbu s5, 0(t0)
  li s6, 128
.Lsecc_mul_bit_loop:
  beqz s6, .Lsecc_mul_next_byte
  bnez s3, .Lsecc_mul_skip_double
  mv a0, s2
  la a1, secc_point_tmp
  jal ra, secp256k1_point_double
  mv s3, a0
  la a0, secc_point_tmp
  mv a1, s2
  jal ra, secp256k1_point_copy64
.Lsecc_mul_skip_double:
  and t0, s5, s6
  beqz t0, .Lsecc_mul_advance_bit
  beqz s3, .Lsecc_mul_add_base
  mv a0, s1
  mv a1, s2
  jal ra, secp256k1_point_copy64
  li s3, 0
  j .Lsecc_mul_advance_bit
.Lsecc_mul_add_base:
  mv a0, s2
  mv a1, s1
  la a2, secc_point_tmp
  jal ra, secp256k1_point_add
  mv s3, a0
  la a0, secc_point_tmp
  mv a1, s2
  jal ra, secp256k1_point_copy64
.Lsecc_mul_advance_bit:
  srli s6, s6, 1
  j .Lsecc_mul_bit_loop
.Lsecc_mul_next_byte:
  addi s4, s4, 1
  j .Lsecc_mul_byte_loop
.Lsecc_mul_done:
  mv a0, s3
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 72
  ret
