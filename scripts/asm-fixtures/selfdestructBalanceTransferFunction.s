selfdestruct_balance_transfer:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                   # origin ptr
  mv s1, a1                   # origin len
  mv s2, a2                   # beneficiary ptr
  mv s3, a3                   # beneficiary len
  mv s4, a4                   # same-address flag
  mv s5, a5                   # origin created in tx flag
  mv s6, a6                   # output base
  sd zero, 0(s6); sd zero, 8(s6)
  addi s7, s6, 16             # origin output ptr
  bnez s4, .Lsdbt_same
  # Different beneficiary: extract origin balance as the beneficiary delta.
  mv a0, s0; mv a1, s1; la a2, aab_bal32
  jal ra, account_extract_balance
  bnez a0, .Lsdbt_fail
  la t0, aab_bal32; la t1, sdbt_delta32
  ld t2, 0(t0); sd t2, 0(t1); ld t2, 8(t0); sd t2, 8(t1)
  ld t2, 16(t0); sd t2, 16(t1); ld t2, 24(t0); sd t2, 24(t1)
  # Set origin balance to zero.
  mv a0, s0; mv a1, s1; li a2, 1; la a3, aab_bal32; li a4, 0
  mv a5, s7; mv a6, s6
  jal ra, account_set_uint_field
  bnez a0, .Lsdbt_fail
  # Credit beneficiary with the extracted origin balance.
  addi t0, s6, 128
  mv a0, s2; mv a1, s3; la a2, sdbt_delta32; mv a3, t0
  addi a4, s6, 8
  jal ra, account_add_balance
  bnez a0, .Lsdbt_fail
  li a0, 0
  j .Lsdbt_ret
.Lsdbt_same:
  bnez s5, .Lsdbt_same_created
  # Same non-created account: move_ether subtracts and adds back, net no-op.
  sd s1, 0(s6); sd s1, 8(s6)
  mv a0, s7; mv a1, s0; mv a2, s1
  jal ra, mset_memcpy
  addi a0, s6, 128; mv a1, s0; mv a2, s1
  jal ra, mset_memcpy
  li a0, 0
  j .Lsdbt_ret
.Lsdbt_same_created:
  # Same created account: move_ether is a no-op, then the created account burns.
  la t0, aab_bal32; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)
  mv a0, s0; mv a1, s1; li a2, 1; mv a3, t0; li a4, 0
  mv a5, s7; mv a6, s6
  jal ra, account_set_uint_field
  bnez a0, .Lsdbt_fail
  ld t0, 0(s6); sd t0, 8(s6)
  addi a0, s6, 128; mv a1, s7; mv a2, t0
  jal ra, mset_memcpy
  li a0, 0
  j .Lsdbt_ret
.Lsdbt_fail:
  li a0, 1
.Lsdbt_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
