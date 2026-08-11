sender_debit_from_gas:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a4                    # eff_gas_price ptr
  mv s1, a5                    # value ptr
  mv s2, a6                    # out debit ptr
  jal ra, tx_gas_result_increments
  mv a1, a2                    # receipt_inc (u64 multiplier)
  mv a0, s0; la a2, sdfg_gascost
  jal ra, u256_mul_u64_be
  la a0, sdfg_gascost; mv a1, s1; mv a2, s2
  jal ra, u256_add_be
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48
  ret
