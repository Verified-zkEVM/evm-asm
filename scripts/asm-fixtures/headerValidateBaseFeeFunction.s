header_validate_base_fee:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a0                   # save header.base_fee ptr
  # expected = eip1559_calc_base_fee_per_gas(...)  → hvbf_expected
  mv a0, a1                   # parent.gas_limit
  mv a1, a2                   # parent.gas_used
  mv a2, a3                   # parent.base_fee
  la a3, hvbf_expected
  jal ra, eip1559_calc_base_fee_per_gas
  bnez a0, .Lhvbf_fail_compute
  # Compare header.base_fee vs expected.
  mv a0, s0
  la a1, hvbf_expected
  jal ra, u256_eq             # a0 = 1 if equal, 0 if not
  beqz a0, .Lhvbf_fail_mismatch
  li a0, 0
  j .Lhvbf_ret
.Lhvbf_fail_mismatch:
  li a0, 1
  j .Lhvbf_ret
.Lhvbf_fail_compute:
  li a0, 2
.Lhvbf_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
