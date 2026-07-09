intrinsic_gas_amsterdam_counts:
  # a0=data ptr, a1=data len, a2=is_creation, a3=access addrs,
  # a4=access slots, a5=authorization count, a6=intrinsic out, a7=floor out
  # 0(sp)=value_nonzero, 8(sp)=is_self_transfer at helper entry
  li t0, 0                    # zero_count
  li t1, 0                    # non_zero_count
  mv t2, a0                   # cursor
  mv t3, a1                   # remaining
.Ligac_loop:
  beqz t3, .Ligac_count_done
  lbu t4, 0(t2)
  bnez t4, .Ligac_nz
  addi t0, t0, 1
  j .Ligac_step
.Ligac_nz:
  addi t1, t1, 1
.Ligac_step:
  addi t2, t2, 1
  addi t3, t3, -1
  j .Ligac_loop
.Ligac_count_done:
  slli t5, t1, 2              # non_zero_count * 4
  add t5, t5, t0              # tokens
  slli t6, t5, 2              # data cost = tokens * 4
  li t4, 12000
  add t6, t6, t4              # intrinsic = base + data
  beqz a2, .Ligac_not_creation
  li t4, 11000                # CREATE_ACCESS
  add t6, t6, t4
  addi t4, a1, 31
  srli t4, t4, 5
  slli t4, t4, 1              # init code cost = 2 * ceil(len / 32)
  add t6, t6, t4
  ld t4, 0(sp)                # value_nonzero
  beqz t4, .Ligac_after_recipient
  li t4, 1756                 # TRANSFER_LOG_COST for creation with value
  add t6, t6, t4
  j .Ligac_after_recipient
.Ligac_not_creation:
  ld t4, 8(sp)                # is_self_transfer
  bnez t4, .Ligac_after_recipient
  li t4, 3000                 # COLD_ACCOUNT_ACCESS for non-self call
  add t6, t6, t4
  ld t4, 0(sp)                # value_nonzero
  beqz t4, .Ligac_after_recipient
  li t4, 6000                 # TRANSFER_LOG_COST + TX_VALUE_COST
  add t6, t6, t4
.Ligac_after_recipient:
  li t4, 3000
  mul t4, a3, t4
  add t6, t6, t4
  li t4, 3000
  mul t4, a4, t4
  add t6, t6, t4
  li t4, 80
  mul t2, a3, t4             # access-list floor tokens: addresses
  li t4, 128
  mul t4, a4, t4             # access-list floor tokens: storage keys
  add t2, t2, t4             # access_tokens
  slli t4, t2, 4             # access-list floor gas = access_tokens * 16
  add t6, t6, t4
  li t4, 15816
  mul t4, a5, t4
  add t6, t6, t4
  sd t6, 0(a6)
  slli t5, a1, 2             # floor calldata tokens = 4 * data_len
  add t5, t5, t2             # total floor tokens
  slli t5, t5, 4             # calldata floor gas = total tokens * 16
  li t4, 12000
  add t5, t5, t4
  sd t5, 0(a7)
  li a0, 0
  ret
