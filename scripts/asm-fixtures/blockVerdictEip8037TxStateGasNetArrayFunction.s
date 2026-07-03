block_verdict_eip8037_tx_state_gas_net_array:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0                   # intrinsic_state_gas ptr
  mv s1, a1                   # executed_state_gas ptr
  mv s2, a2                   # state_refund ptr
  mv s3, a3                   # tx_status ptr (1 success, 0 error)
  mv s4, a4                   # is_creation ptr
  mv s5, a5                   # count
  mv s6, a6                   # output ptr
  li s7, 0                    # i
.Lbve8037sg_loop:
  beq s7, s5, .Lbve8037sg_ok
  slli s8, s7, 3
  add t0, s0, s8; ld a0, 0(t0)        # intrinsic_state_gas[i]
  add t0, s1, s8; ld a1, 0(t0)        # executed_state_gas[i]
  add t0, s2, s8; ld a2, 0(t0)        # state_refund[i]
  add t0, s3, s8; ld t1, 0(t0); seqz a3, t1  # error_flag = tx_status[i] == 0
  add t0, s4, s8; ld a4, 0(t0)        # is_creation[i]
  add a5, s6, s8                      # out[i]
  jal ra, eip8037_tx_state_gas
  bnez a0, .Lbve8037sg_fail
  addi s7, s7, 1; j .Lbve8037sg_loop
.Lbve8037sg_ok:
  li a0, 0; li a1, 0; j .Lbve8037sg_ret
.Lbve8037sg_fail:
  li a0, 1; mv a1, s7
.Lbve8037sg_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 80
  ret
