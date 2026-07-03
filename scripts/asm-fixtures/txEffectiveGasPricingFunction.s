tx_effective_gas_pricing:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a2                   # base_fee ptr
  mv s1, a3                   # effective_gas_price out
  mv s2, a4                   # priority_fee out
  sd zero,  0(s1); sd zero,  8(s1); sd zero, 16(s1); sd zero, 24(s1)
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  la a2, tefgp_max_priority
  la a3, tefgp_max_fee
  jal ra, tx_extract_gas_pricing
  beqz a0, .Ltefgp_have_fields
  li a0, 1; j .Ltefgp_ret
.Ltefgp_have_fields:
  # Typed EIP-1559-family transactions require max_fee >= max_priority;
  # legacy/EIP-2930 have equal normalized values, so this is harmless there.
  la a0, tefgp_max_fee
  la a1, tefgp_max_priority
  la a2, tefgp_tmp
  jal ra, u256_sub_be
  beqz a0, .Ltefgp_fee_order_ok
  li a0, 2; j .Ltefgp_ret
.Ltefgp_fee_order_ok:
  # priority_fee = min(max_priority, max_fee - base_fee), rejects max_fee < base_fee.
  la a0, tefgp_max_priority
  la a1, tefgp_max_fee
  mv a2, s0
  mv a3, s2
  jal ra, priority_fee_per_gas_eip1559
  beqz a0, .Ltefgp_have_priority
  sd zero,  0(s2); sd zero,  8(s2); sd zero, 16(s2); sd zero, 24(s2)
  li a0, 3; j .Ltefgp_ret
.Ltefgp_have_priority:
  mv a0, s0
  mv a1, s2
  mv a2, s1
  jal ra, u256_add_be
  beqz a0, .Ltefgp_ok
  sd zero,  0(s1); sd zero,  8(s1); sd zero, 16(s1); sd zero, 24(s1)
  li a0, 4; j .Ltefgp_ret
.Ltefgp_ok:
  li a0, 0
.Ltefgp_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
