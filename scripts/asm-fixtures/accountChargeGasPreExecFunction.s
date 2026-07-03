account_charge_gas_pre_exec:
  addi sp, sp, -24
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a0                   # balance ptr
  mv s1, a3                   # nonce ptr (in-out)
  # gas_fee = effective_gas_price × gas_limit
  mv a0, a1
  mv a1, a2
  la a2, acpg_gas_fee
  jal ra, u256_mul_u64_be
  bnez a0, .Lacpg_fail_mul
  # balance -= gas_fee
  mv a0, s0
  la a1, acpg_gas_fee
  mv a2, s0
  jal ra, u256_sub_be
  bnez a0, .Lacpg_fail_sub
  # *nonce_ptr += 1
  ld t0, 0(s1)
  addi t0, t0, 1
  sd t0, 0(s1)
  li a0, 0
  j .Lacpg_ret
.Lacpg_fail_mul:
  li a0, 1
  j .Lacpg_ret
.Lacpg_fail_sub:
  li a0, 2
.Lacpg_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 24
  ret
