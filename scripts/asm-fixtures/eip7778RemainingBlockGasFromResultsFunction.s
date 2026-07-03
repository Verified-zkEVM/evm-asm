eip7778_remaining_block_gas_from_results:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp)
  mv s8, a7                   # .6.5.2: per-tx intrinsic_state ptr (0 = none) -> threaded to the check
  mv s0, a0                   # block_gas_limit
  mv s1, a1                   # tx_gas_limits ptr
  mv s2, a2                   # gas_left ptr
  mv s3, a3                   # refund_counter ptr
  mv s4, a4                   # calldata_floor ptr
  mv s5, a5                   # count
  mv s6, a6                   # scratch block increments ptr
  li s7, 0                    # i
.Le7778rr_loop:
  beq s7, s5, .Le7778rr_check
  slli t0, s7, 3
  add t1, s1, t0
  ld a0, 0(t1)                # tx_gas_limit
  add t1, s2, t0
  ld a1, 0(t1)                # gas_left
  add t1, s3, t0
  ld a2, 0(t1)                # refund_counter
  add t1, s4, t0
  ld a3, 0(t1)                # calldata_floor_gas_cost
  jal ra, tx_gas_result_increments
  bnez a0, .Le7778rr_bad_result
  slli t0, s7, 3
  add t1, s6, t0
  sd a1, 0(t1)                # exact block_gas_used_in_tx
  addi s7, s7, 1
  j .Le7778rr_loop
.Le7778rr_check:
  mv a0, s0
  mv a1, s1
  mv a2, s6
  mv a3, s5
  mv a4, s8                   # .6.5.2: intrinsic_state ptr (0 = none)
  jal ra, eip7778_remaining_block_gas_check
  j .Le7778rr_ret
.Le7778rr_bad_result:
  li a0, 3
  addi a1, s7, 1
  li a2, 0
.Le7778rr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp)
  addi sp, sp, 80
  ret
