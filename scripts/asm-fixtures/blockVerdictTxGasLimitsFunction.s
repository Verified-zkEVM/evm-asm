block_verdict_tx_gas_limits:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # execution payload
  mv s1, a1                   # gas limit output array
  mv s2, a2                   # max_count
  la t0, bvgr_status; sd zero, 0(t0)
  la t0, bvgr_count; sd zero, 0(t0)
  la t0, bvgr_fail_index; sd zero, 0(t0)
  la t0, bvgr_tx_type; sd zero, 0(t0)
  addi a0, s0, 504; jal ra, bgv_u32le
  mv s3, a0                   # transactions_offset
  addi a0, s0, 508; jal ra, bgv_u32le
  mv s4, a0                   # withdrawals_offset
  bleu s4, s3, .Lbvgr_ok_zero # no transactions
  add s5, s0, s3              # tx list ptr
  sub s6, s4, s3              # tx list byte length
  li t0, 4; bltu s6, t0, .Lbvgr_malformed
  mv a0, s5; jal ra, bgv_u32le
  andi t0, a0, 3; bnez t0, .Lbvgr_malformed
  bgtu a0, s6, .Lbvgr_malformed
  srli s7, a0, 2              # tx_count
  la t0, bvgr_count; sd s7, 0(t0)
  bgtu s7, s2, .Lbvgr_capacity
  beqz s7, .Lbvgr_ok
  mv s8, zero                 # tx index
  slli s11, s7, 2             # minimum item offset = offset table len
.Lbvgr_loop:
  beq s8, s7, .Lbvgr_ok
  slli t0, s8, 2
  add a0, s5, t0
  jal ra, bgv_u32le
  mv s9, a0                   # current tx offset
  bltu s9, s11, .Lbvgr_malformed_tx
  bgtu s9, s6, .Lbvgr_malformed_tx
  addi t0, s8, 1
  beq t0, s7, .Lbvgr_last_tx
  slli t1, t0, 2
  add a0, s5, t1
  jal ra, bgv_u32le
  mv s10, a0                  # next tx offset
  j .Lbvgr_have_next
.Lbvgr_last_tx:
  mv s10, s6                  # final tx ends at list end
.Lbvgr_have_next:
  bltu s10, s9, .Lbvgr_malformed_tx
  bgtu s10, s6, .Lbvgr_malformed_tx
  add t0, s5, s9              # tx ptr
  sub t1, s10, s9             # tx len
  mv a0, t0; mv a1, t1; la a2, bvgr_tx_type; la a3, bvgr_tx_inner
  jal ra, tx_type_dispatch
  bnez a0, .Lbvgr_type_fail
  add t0, s5, s9
  sub t1, s10, s9
  mv a0, t0; mv a1, t1; la a2, bvgr_nonce; la a3, bvgr_gas
  jal ra, tx_extract_nonce_and_gas
  bnez a0, .Lbvgr_extract_fail
  slli t0, s8, 3
  add t1, s1, t0
  la t2, bvgr_gas; ld t3, 0(t2)
  sd t3, 0(t1)
  addi s8, s8, 1
  j .Lbvgr_loop
.Lbvgr_ok_zero:
  mv s7, zero
.Lbvgr_ok:
  li a0, 0; mv a1, s7; li a2, 0; la t0, bvgr_tx_type; ld a3, 0(t0)
  j .Lbvgr_store_ret
.Lbvgr_malformed_tx:
  addi a2, s8, 1; li a0, 1; mv a1, s7; j .Lbvgr_store_ret
.Lbvgr_malformed:
  li a0, 1; li a1, 0; li a2, 0; li a3, 0; j .Lbvgr_store_ret
.Lbvgr_capacity:
  li a0, 2; mv a1, s7; li a2, 0; li a3, 0; j .Lbvgr_store_ret
.Lbvgr_type_fail:
  li a0, 3; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)
  j .Lbvgr_store_ret
.Lbvgr_extract_fail:
  li a0, 4; mv a1, s7; addi a2, s8, 1; la t0, bvgr_tx_type; ld a3, 0(t0)
.Lbvgr_store_ret:
  la t0, bvgr_status; sd a0, 0(t0)
  la t0, bvgr_count; sd a1, 0(t0)
  la t0, bvgr_fail_index; sd a2, 0(t0)
  la t0, bvgr_tx_type; sd a3, 0(t0)
.Lbvgr_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
