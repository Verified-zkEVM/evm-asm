tx_cost_compute:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a2                   # value ptr
  mv s1, a3                   # out ptr
  # Step 1: out = effective_gas_price × gas_limit.
  mv a2, s1
  jal ra, u256_mul_u64_be
  bnez a0, .Ltcc_fail
  # Step 2: out = out + value.
  mv a0, s1
  mv a1, s0
  mv a2, s1
  jal ra, u256_add_be
  bnez a0, .Ltcc_fail
  li a0, 0
  j .Ltcc_ret
.Ltcc_fail:
  li a0, 1
.Ltcc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
