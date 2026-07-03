eip1559_calc_base_fee_per_gas:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a2                    # base_fee ptr
  mv s1, a3                    # out ptr
  srli s2, a0, 1               # parent_gas_target = parent.gas_limit / 2
  beq a1, s2, .Lebf_eq         # gas_used == target → expected = base_fee
  li s4, 0                     # path flag: 0 = below, 1 = above
  bgtu a1, s2, .Lebf_set_above
  beqz a1, .Lebf_below_zero_used
  sub s3, s2, a1               # below: delta = target - gas_used
  j .Lebf_compute
.Lebf_set_above:
  li s4, 1
  sub s3, a1, s2               # above: delta = gas_used - target
.Lebf_compute:
  # parent_fee_gas_delta = parent.base_fee × gas_used_delta
  mv a0, s0
  mv a1, s3
  mv a2, s1
  jal ra, u256_mul_u64_be
  bnez a0, .Lebf_fail
  # target_fee_gas_delta = parent_fee_gas_delta / parent_gas_target
  mv a0, s1
  mv a1, s2
  mv a2, s1
  jal ra, u256_div_u64_be
  # base_fee_delta = target_fee_gas_delta / 8
  mv a0, s1
  li a1, 8
  mv a2, s1
  jal ra, u256_div_u64_be
  # If above path: max(delta, 1).
  beqz s4, .Lebf_apply
  mv a0, s1
  jal ra, u256_is_zero
  beqz a0, .Lebf_apply
  li a0, 1
  mv a1, s1
  jal ra, u256_from_u64_be
  j .Lebf_apply
.Lebf_below_zero_used:
  # When parent_gas_used = 0, gas_used_delta = target, so
  # (base_fee * target) / target = base_fee exactly. Avoid the large
  # intermediate product for very high test gas limits.
  mv a0, s0
  li a1, 8
  mv a2, s1
  jal ra, u256_div_u64_be
.Lebf_apply:
  beqz s4, .Lebf_sub_path
  # above: out = base_fee + delta
  mv a0, s0
  mv a1, s1
  mv a2, s1
  jal ra, u256_add_be
  bnez a0, .Lebf_fail
  li a0, 0
  j .Lebf_ret
.Lebf_sub_path:
  # below: out = base_fee - delta
  mv a0, s0
  mv a1, s1
  mv a2, s1
  jal ra, u256_sub_be
  bnez a0, .Lebf_fail
  li a0, 0
  j .Lebf_ret
.Lebf_eq:
  # Copy base_fee to out (32 B chunk copy).
  ld t0,  0(s0); sd t0,  0(s1)
  ld t0,  8(s0); sd t0,  8(s1)
  ld t0, 16(s0); sd t0, 16(s1)
  ld t0, 24(s0); sd t0, 24(s1)
  li a0, 0
  j .Lebf_ret
.Lebf_fail:
  li a0, 1
.Lebf_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 56
  ret
