priority_fee_per_gas_eip1559:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                   # max_priority ptr
  mv s1, a1                   # max_fee ptr
  mv s2, a2                   # base_fee ptr
  mv s3, a3                   # out ptr
  # surplus = max_fee - base_fee  (store in out)
  mv a0, s1; mv a1, s2; mv a2, s3
  jal ra, u256_sub_be
  bnez a0, .Lpfee_fail        # borrow -> max_fee < base_fee
  # priority_fee = min(max_priority, surplus); aliasing OK
  mv a0, s0; mv a1, s3; mv a2, s3
  jal ra, u256_min
  li a0, 0
  j .Lpfee_ret
.Lpfee_fail:
  li a0, 1
.Lpfee_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
