effective_gas_price_eip1559:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a2                   # base_fee ptr
  mv s1, a3                   # out ptr
  # Step 1: priority_fee = priority_fee_per_gas_eip1559(...)
  jal ra, priority_fee_per_gas_eip1559
  bnez a0, .Legpe_fail
  # Step 2: effective = base_fee + priority_fee   (out = base + out)
  mv a0, s0
  mv a1, s1
  mv a2, s1
  jal ra, u256_add_be         # overflow flag in a0 (always 0 in practice)
  li a0, 0
  j .Legpe_ret
.Legpe_fail:
  li a0, 1
.Legpe_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
