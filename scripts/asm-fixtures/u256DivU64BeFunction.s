u256_div_u64_be:
  li t0, 0                   # remainder
  li t1, 0                   # byte index (MSB → LSB)
.Lu256d_loop:
  li t2, 32
  beq t1, t2, .Lu256d_done
  add t3, a0, t1
  lbu t4, 0(t3)              # src[i]
  li t6, 0                    # quotient byte
  li t2, 8                    # restoring bit steps
.Lu256d_bits:
  beq t2, zero, .Lu256d_store
  srli t3, t0, 63             # carry-out before the shift
  slli t0, t0, 1
  srli t5, t4, 7
  andi t5, t5, 1
  slli t4, t4, 1
  or t0, t0, t5
  sltu t5, t0, a1
  xori t5, t5, 1
  or t5, t5, t3
  slli t6, t6, 1
  or t6, t6, t5
  sub t3, zero, t5
  and t3, t3, a1
  sub t0, t0, t3
  addi t2, t2, -1
  j .Lu256d_bits
.Lu256d_store:
  add t3, a2, t1
  sb t6, 0(t3)               # out[i] = q_byte
  addi t1, t1, 1
  j .Lu256d_loop
.Lu256d_done:
  mv a0, t0                  # remainder
  ret
