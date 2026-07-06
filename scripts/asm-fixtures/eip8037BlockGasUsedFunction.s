eip8037_block_gas_used:
  # a0=regular_inc ptr, a1=tx_state_gas ptr, a2=count,
  # a3=header_gas_used, a4=block_gas_used_out
  mv t0, a0                   # regular_inc ptr
  mv t1, a1                   # tx_state_gas ptr
  mv t2, a2                   # count
  li t3, 0                    # i
  li t4, 0                    # block_regular
  li t5, 0                    # block_state
.Le8037bg_loop:
  beq t3, t2, .Le8037bg_done
  slli t6, t3, 3
  add a5, t0, t6
  ld a5, 0(a5)               # regular increment
  add a6, t4, a5
  bltu a6, t4, .Le8037bg_overflow
  mv t4, a6                  # block_regular += regular increment
  add a5, t1, t6
  ld a5, 0(a5)               # tx_state_gas
  add a6, t5, a5
  bltu a6, t5, .Le8037bg_overflow
  mv t5, a6                  # block_state += tx_state_gas
  addi t3, t3, 1
  j .Le8037bg_loop
.Le8037bg_done:
  mv a5, t4                  # block_gas_used = block_regular
  bgeu t4, t5, .Le8037bg_have_max
  mv a5, t5                  # block_gas_used = block_state
.Le8037bg_have_max:
  sd a5, 0(a4)
  bne a5, a3, .Le8037bg_mismatch
  li a0, 0
  mv a1, a5
  ret
.Le8037bg_mismatch:
  li a0, 1
  mv a1, a5
  ret
.Le8037bg_overflow:
  sd zero, 0(a4)
  li a0, 2
  li a1, 0
  ret
