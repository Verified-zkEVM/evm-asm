block_verdict_eip8037_tx_state_gas_net_array:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  mv s3, a3
  li s4, 0
.Le8037nga_loop:
  beq s4, s2, .Le8037nga_ok
  slli t0, s4, 3
  add t1, s0, t0
  ld a0, 0(t1)
  add t1, s1, t0
  ld a1, 0(t1)
  add a5, s3, t0
  jal ra, eip8037_tx_state_gas
  addi s4, s4, 1
  j .Le8037nga_loop
.Le8037nga_ok:
  li a0, 0
  li a1, 0
  ld ra, 0(sp)
  ld s0, 8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
