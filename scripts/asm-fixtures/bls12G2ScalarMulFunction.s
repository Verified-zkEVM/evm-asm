blsg2_scalar_mul:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                      # scalar bytes
  mv s7, a1                      # scalar byte length
  mv s1, a2                      # base point
  mv s2, a3                      # accumulator/output
  mv a0, s2
  jal ra, blsg2_zero192
  li s3, 1                       # accumulator is infinity
  li s4, 0                       # byte index
.Lblsg2_mul_byte_loop:
  bgeu s4, s7, .Lblsg2_mul_done
  add t0, s0, s4
  lbu s5, 0(t0)
  li s6, 128
.Lblsg2_mul_bit_loop:
  beqz s6, .Lblsg2_mul_next_byte
  bnez s3, .Lblsg2_mul_skip_double
  mv a0, s2
  mv a1, s2
  jal ra, blsg2_point_dbl        # alias-safe in-place double
  mv s3, a0
.Lblsg2_mul_skip_double:
  and t0, s5, s6
  beqz t0, .Lblsg2_mul_advance_bit
  beqz s3, .Lblsg2_mul_add_base
  mv a0, s1
  mv a1, s2
  jal ra, blsg2_copy192
  mv a0, s2
  li a1, 192
  jal ra, blsg_is_zero_n
  mv s3, a0                      # base may itself be infinity
  j .Lblsg2_mul_advance_bit
.Lblsg2_mul_add_base:
  mv a0, s2
  mv a1, s1
  mv a2, s2
  jal ra, blsg2_point_add        # alias-safe in-place add
  mv s3, a0
.Lblsg2_mul_advance_bit:
  srli s6, s6, 1
  j .Lblsg2_mul_bit_loop
.Lblsg2_mul_next_byte:
  addi s4, s4, 1
  j .Lblsg2_mul_byte_loop
.Lblsg2_mul_done:
  mv a0, s3
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
