header_validate_excess_blob_gas:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # this.excess_blob_gas
  mv s1, a1                   # parent.blob_gas_used
  mv s2, a2                   # parent.excess_blob_gas
  mv s3, a3                   # parent.base_fee_per_gas ptr
  add s4, s2, s1              # parent_blob_gas
  bltu s4, s2, .Lhvebg_overflow
  li t0, 1835008              # 14 * 131072
  bltu s4, t0, .Lhvebg_expected_zero
  mv a0, s2
  la a1, hvebg_threshold
  jal ra, amsterdam_blob_gas_price_u256   # threshold = blob gas price (u256)
  bnez a0, .Lhvebg_overflow
  la a0, hvebg_threshold
  li a1, 16
  la a2, hvebg_threshold
  jal ra, u256_mul_u64_be     # threshold = 16 * price
  bnez a0, .Lhvebg_overflow
  la a0, hvebg_threshold
  mv a1, s3
  la a2, u256m_acc            # u256_lt_be writes the verdict to *a2 (a0 is status)
  jal ra, u256_lt_be          # [u256m_acc] = 1 iff threshold < parent_base_fee
  la t0, u256m_acc
  ld t0, 0(t0)
  beqz t0, .Lhvebg_normal
  li t0, 2635249153387078802  # (2^64-1) // 7
  bltu t0, s1, .Lhvebg_overflow  # spec: U64 used * 7 raises OverflowError
  li t0, 3
  divu t1, s1, t0             # used * 7 // 21 == used // 3
  add s5, s2, t1
  bltu s5, s2, .Lhvebg_overflow
  j .Lhvebg_compare
.Lhvebg_normal:
  li t0, 1835008
  sub s5, s4, t0
  j .Lhvebg_compare
.Lhvebg_expected_zero:
  li s5, 0
.Lhvebg_compare:
  bne s0, s5, .Lhvebg_mismatch
  li a0, 0
  j .Lhvebg_ret
.Lhvebg_overflow:
  li a0, 1
  j .Lhvebg_ret
.Lhvebg_mismatch:
  li a0, 2
.Lhvebg_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
