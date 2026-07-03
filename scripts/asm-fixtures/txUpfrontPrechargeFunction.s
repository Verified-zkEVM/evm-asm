tx_upfront_precharge:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # base_fee ptr
  mv s3, a3                   # sender balance ptr
  mv s4, a4                   # sender nonce ptr
  la t0, txup_nonce; sd zero, 0(t0)
  la t0, txup_gas_limit; sd zero, 0(t0)
  la t0, txup_effective_gas_price
  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)
  la t0, txup_priority_fee
  sd zero,  0(t0); sd zero,  8(t0); sd zero, 16(t0); sd zero, 24(t0)
  # Step 1: parse nonce and gas_limit.
  mv a0, s0; mv a1, s1; la a2, txup_nonce; la a3, txup_gas_limit
  jal ra, tx_extract_nonce_and_gas
  beqz a0, .Ltxup_have_gas
  li a0, 10
  j .Ltxup_ret
.Ltxup_have_gas:
  # Step 2: compute effective gas price and priority fee.
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, txup_effective_gas_price; la a4, txup_priority_fee
  jal ra, tx_effective_gas_pricing
  beqz a0, .Ltxup_have_pricing
  li a0, 20
  j .Ltxup_ret
.Ltxup_have_pricing:
  # Step 3: deduct effective_gas_price * gas_limit and increment nonce.
  mv a0, s3; la a1, txup_effective_gas_price
  la t0, txup_gas_limit; ld a2, 0(t0)
  mv a3, s4
  jal ra, account_charge_gas_pre_exec
  beqz a0, .Ltxup_ok
  li t0, 1; beq a0, t0, .Ltxup_fail_mul
  li a0, 32
  j .Ltxup_ret
.Ltxup_fail_mul:
  li a0, 31
  j .Ltxup_ret
.Ltxup_ok:
  li a0, 0
.Ltxup_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
