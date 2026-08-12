blsg_scalar_mul:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                      # scalar bytes
  mv s7, a1                      # scalar byte length
  mv s1, a2                      # base point (BE)
  mv s2, a3                      # output (BE)
  mv a0, s1
  la a1, blsg_le_base
  jal ra, blsg_be_to_le
  addi a0, s1, 48
  la a1, blsg_le_base
  addi a1, a1, 48
  jal ra, blsg_be_to_le
  la a0, blsg_le_acc
  jal ra, blsg_zero96
  li s3, 1                       # accumulator is infinity
  li s4, 0                       # byte index
.Lblsg_mul_byte_loop:
  bgeu s4, s7, .Lblsg_mul_done
  add t0, s0, s4
  lbu s5, 0(t0)
  li s6, 128
.Lblsg_mul_bit_loop:
  beqz s6, .Lblsg_mul_next_byte
  bnez s3, .Lblsg_mul_skip_double
  la a0, blsg_le_acc
  la a1, blsg_le_acc
  jal ra, blsg_le_dbl            # alias-safe in-place double
  mv s3, a0
.Lblsg_mul_skip_double:
  and t0, s5, s6
  beqz t0, .Lblsg_mul_advance_bit
  beqz s3, .Lblsg_mul_add_base
  la a0, blsg_le_base
  la a1, blsg_le_acc
  jal ra, blsg_copy96
  la a0, blsg_le_acc
  li a1, 96
  jal ra, blsg_is_zero_n
  mv s3, a0                      # base may itself be (0,0)
  j .Lblsg_mul_advance_bit
.Lblsg_mul_add_base:
  la a0, blsg_le_acc
  la a1, blsg_le_base
  la a2, blsg_le_acc
  jal ra, blsg_le_add            # alias-safe in-place add
  mv s3, a0
.Lblsg_mul_advance_bit:
  srli s6, s6, 1
  j .Lblsg_mul_bit_loop
.Lblsg_mul_next_byte:
  addi s4, s4, 1
  j .Lblsg_mul_byte_loop
.Lblsg_mul_done:
  bnez s3, .Lblsg_mul_inf_out
  la a0, blsg_le_acc
  mv a1, s2
  jal ra, blsg_le_to_be
  la a0, blsg_le_acc
  addi a0, a0, 48
  addi a1, s2, 48
  jal ra, blsg_le_to_be
  li a0, 0
  j .Lblsg_mul_ret
.Lblsg_mul_inf_out:
  mv a0, s2
  jal ra, blsg_zero96
  li a0, 1
.Lblsg_mul_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
