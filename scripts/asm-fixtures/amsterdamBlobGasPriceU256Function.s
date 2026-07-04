amsterdam_blob_gas_price_u256:
  addi sp, sp, -128
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # numerator = excess_blob_gas
  mv s5, a1                   # caller output price ptr (u256 BE)
  li s1, 11684671             # Amsterdam BLOB_BASE_FEE_UPDATE_FRACTION
  li s2, 1                    # i
  addi s3, sp, 64             # numerator_accumulated (u256 scratch)
  addi s4, sp, 96             # output accumulator (u256 scratch)
  mv a0, s1; mv a1, s3; jal ra, u256_from_u64_be   # accum = denominator
  li a0, 0; mv a1, s4; jal ra, u256_from_u64_be    # output = 0
.Labgpu_loop:
  mv a0, s3; jal ra, u256_is_zero
  bnez a0, .Labgpu_done
  mv a0, s4; mv a1, s3; mv a2, s4; jal ra, u256_add_be   # output += accum
  bnez a0, .Labgpu_overflow
  mv a0, s3; mv a1, s0; mv a2, s3; jal ra, u256_mul_u64_be  # accum *= excess
  bnez a0, .Labgpu_overflow
  mulhu t0, s1, s2; bnez t0, .Labgpu_overflow         # deni = denom*i fits u64
  mul t1, s1, s2
  srli t0, t1, 56; bnez t0, .Labgpu_overflow          # and within div helper's 2^56
  mv a0, s3; mv a1, t1; mv a2, s3; jal ra, u256_div_u64_be  # accum //= deni
  addi s2, s2, 1
  j .Labgpu_loop
.Labgpu_done:
  mv a0, s4; mv a1, s1; mv a2, s5; jal ra, u256_div_u64_be  # price = output//denom
  li a0, 0
  j .Labgpu_u256_ret
.Labgpu_overflow:
  li a0, 1
.Labgpu_u256_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 128
  ret
