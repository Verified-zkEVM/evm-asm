amsterdam_blob_gas_price:
  addi sp, sp, -48
  sd s0,  0(sp); sd s1,  8(sp); sd s2, 16(sp)
  sd s3, 24(sp); sd s4, 32(sp)
  mv s0, a0                   # numerator = excess_blob_gas
  li s1, 11684671             # Amsterdam BLOB_BASE_FEE_UPDATE_FRACTION
  li s2, 1                    # i
  li s3, 0                    # output accumulator
  mv s4, s1                   # numerator_accumulated = denominator
.Labgp_loop:
  beqz s4, .Labgp_done
  add t0, s3, s4              # output += numerator_accumulated
  bltu t0, s3, .Labgp_overflow
  mv s3, t0
  mulhu t3, s4, s0            # hi half of accum * numerator (128-bit product)
  mul t4, s4, s0             # lo half of accum * numerator
  mulhu t0, s1, s2            # high half of denominator * i
  bnez t0, .Labgp_overflow
  mul t2, s1, s2              # deni = denominator * i
  beqz t2, .Labgp_overflow
  bgeu t3, t2, .Labgp_overflow # hi >= deni => quotient exceeds u64
  mv t5, t3                   # rem = hi (hi < deni guaranteed)
  li t6, 0                    # q = 0
  li t1, 64                   # 64 division iterations
.Labgp_div:
  srli t0, t4, 63             # lobit = MSB of lo
  srli t3, t5, 63             # topbit = carry-out of rem << 1
  slli t5, t5, 1              # rem <<= 1
  or t5, t5, t0               # rem |= lobit
  slli t4, t4, 1              # consume next lo bit
  slli t6, t6, 1              # q <<= 1
  bnez t3, .Labgp_div_sub     # carry-out => true rem >= 2^64 > deni
  bltu t5, t2, .Labgp_div_next
.Labgp_div_sub:
  sub t5, t5, t2              # rem -= deni (u64 wrap exact when topbit set)
  ori t6, t6, 1               # q |= 1
.Labgp_div_next:
  addi t1, t1, -1
  bnez t1, .Labgp_div
  mv s4, t6                   # next numerator_accumulated
  addi t0, s2, 1
  beqz t0, .Labgp_overflow
  mv s2, t0
  j .Labgp_loop
.Labgp_done:
  divu a1, s3, s1             # output // denominator
  li a0, 0
  j .Labgp_ret
.Labgp_overflow:
  li a0, 1
  li a1, 0
.Labgp_ret:
  ld s0,  0(sp); ld s1,  8(sp); ld s2, 16(sp)
  ld s3, 24(sp); ld s4, 32(sp)
  addi sp, sp, 48
  ret
