block_verdict_gas_result_arena_prepare:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # execution payload
  mv s1, a1                   # runtime gas_left ptr
  mv s2, a2                   # runtime refund_counter ptr
  mv s3, a3                   # runtime calldata_floor ptr
  mv s4, a4                   # runtime count
  mv s5, a5                   # arena capacity
  la t0, bvgr_arena_status; sd zero, 0(t0)
  la t0, bvgr_arena_tx_count; sd zero, 0(t0)
  la t0, bvgr_arena_runtime_count; sd s4, 0(t0)
  la t0, bvgr_arena_fail_index; sd zero, 0(t0)
  la t0, bvgr_arena_substatus; sd zero, 0(t0)
  la a1, bvgr_tx_gas_limits
  mv a2, s5
  mv a0, s0
  jal ra, block_verdict_tx_gas_limits
  bnez a0, .Lbvgr_arena_tx_fail
  mv s6, a1                   # transaction count
  la t0, bvgr_arena_tx_count; sd s6, 0(t0)
  bne s4, s6, .Lbvgr_arena_count_mismatch
  beqz s6, .Lbvgr_arena_ok
  beqz s1, .Lbvgr_arena_missing_runtime
  beqz s2, .Lbvgr_arena_missing_runtime
  beqz s3, .Lbvgr_arena_missing_runtime
  mv s7, zero                 # index
.Lbvgr_arena_loop:
  beq s7, s6, .Lbvgr_arena_ok
  slli t0, s7, 3
  la t1, bvgr_tx_gas_limits; add t1, t1, t0; ld s8, 0(t1)
  add t1, s1, t0; ld s9, 0(t1)
  add t1, s2, t0; ld s10, 0(t1)
  add t1, s3, t0; ld s11, 0(t1)
  la t1, bvgr_gas_left; add t1, t1, t0; sd s9, 0(t1)
  la t1, bvgr_refund_counter; add t1, t1, t0; sd s10, 0(t1)
  la t1, bvgr_calldata_floor; add t1, t1, t0; sd s11, 0(t1)
  mv a0, s8; mv a1, s9; mv a2, s10; mv a3, s11
  jal ra, tx_gas_result_increments
  bnez a0, .Lbvgr_arena_bad_result
  slli t0, s7, 3
  la t1, bvgr_block_gas_increments; add t1, t1, t0; sd a1, 0(t1)
  la t1, bvgr_receipt_gas_increments; add t1, t1, t0; sd a2, 0(t1)
  la t1, bvgr_before_refund; add t1, t1, t0; sd a3, 0(t1)
  la t1, bvgr_applied_refund; add t1, t1, t0; sd a4, 0(t1)
  addi s7, s7, 1
  j .Lbvgr_arena_loop
.Lbvgr_arena_ok:
  li a0, 0; mv a1, s6; li a2, 0; li a3, 0; j .Lbvgr_arena_store_ret
.Lbvgr_arena_tx_fail:
  mv t0, a0; mv t1, a1; mv t2, a2
  li a0, 1; mv a1, t1; mv a2, t2; mv a3, t0; j .Lbvgr_arena_store_ret
.Lbvgr_arena_count_mismatch:
  li a0, 2; mv a1, s6; li a2, 0; mv a3, s4; j .Lbvgr_arena_store_ret
.Lbvgr_arena_missing_runtime:
  li a0, 3; mv a1, s6; li a2, 0; li a3, 0; j .Lbvgr_arena_store_ret
.Lbvgr_arena_bad_result:
  mv t0, a0
  li a0, 4; mv a1, s6; addi a2, s7, 1; mv a3, t0
.Lbvgr_arena_store_ret:
  la t0, bvgr_arena_status; sd a0, 0(t0)
  la t0, bvgr_arena_tx_count; sd a1, 0(t0)
  la t0, bvgr_arena_fail_index; sd a2, 0(t0)
  la t0, bvgr_arena_substatus; sd a3, 0(t0)
.Lbvgr_arena_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
