block_verdict_tx_state_gas_array:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # tx-section ptr
  mv s1, a1                   # tx-section len
  mv s2, a2                   # expected count
  mv s3, a3                   # out array
  mv s8, a4                   # optional BAL ptr
  mv s9, a5                   # BAL len
  mv s10, a6                  # chain id
  li t0, 4; bltu s1, t0, .Lbvtsg_malformed
  mv a0, s0; jal ra, bgv_u32le             # first offset = 4 * tx_count
  andi t0, a0, 3; bnez t0, .Lbvtsg_malformed
  bgtu a0, s1, .Lbvtsg_malformed
  srli s4, a0, 2              # tx_count
  bne s4, s2, .Lbvtsg_mismatch
  beqz s4, .Lbvtsg_ok
  mv s5, zero                 # index
.Lbvtsg_loop:
  beq s5, s4, .Lbvtsg_ok
  slli t0, s5, 2; add a0, s0, t0; jal ra, bgv_u32le; mv s6, a0   # cur offset
  slli t0, s4, 2; bltu s6, t0, .Lbvtsg_malformed                 # >= offset-table end
  bgtu s6, s1, .Lbvtsg_malformed
  addi t0, s5, 1; beq t0, s4, .Lbvtsg_last
  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le; mv s7, a0   # next offset
  j .Lbvtsg_have
.Lbvtsg_last:
  mv s7, s1                   # final tx ends at section end
.Lbvtsg_have:
  bltu s7, s6, .Lbvtsg_malformed
  bgtu s7, s1, .Lbvtsg_malformed
  add a0, s0, s6              # tx ptr
  sub a1, s7, s6             # tx len
  slli t0, s5, 3; add a2, s3, t0   # &out[i]
  jal ra, tx_intrinsic_state_gas
  bnez a0, .Lbvtsg_tx_fail
  beqz s8, .Lbvtsg_after_refund
  add a0, s0, s6; sub a1, s7, s6; mv a2, s8; mv a3, s9; mv a4, s10; addi a5, s5, 1
  jal ra, tx_eip7702_existing_authority_refund
  slli t0, s5, 3; add t1, s3, t0; ld t2, 0(t1); bgtu a0, t2, .Lbvtsg_refund_clamp
  sub t2, t2, a0; sd t2, 0(t1); j .Lbvtsg_after_refund
.Lbvtsg_refund_clamp:
  sd zero, 0(t1)
.Lbvtsg_after_refund:
  addi s5, s5, 1; j .Lbvtsg_loop
.Lbvtsg_ok:
  li a0, 0; j .Lbvtsg_ret
.Lbvtsg_malformed:
  li a0, 1; j .Lbvtsg_ret
.Lbvtsg_mismatch:
  li a0, 2; j .Lbvtsg_ret
.Lbvtsg_tx_fail:
  li a0, 3
.Lbvtsg_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
