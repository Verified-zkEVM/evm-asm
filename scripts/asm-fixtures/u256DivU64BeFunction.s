u256_div_u64_be:
  li t0, 0                   # carry (< b)
  li t1, 0                   # byte index (MSB → LSB)
.Lu256d_loop:
  li t2, 32
  beq t1, t2, .Lu256d_done
  add t3, a0, t1
  lbu t4, 0(t3)              # src[i]
  slli t5, t0, 8
  or t5, t5, t4              # num = (carry << 8) | src[i]
  divu t6, t5, a1            # q_byte = num / b  (< 256)
  remu t0, t5, a1            # new carry = num mod b
  add t3, a2, t1
  sb t6, 0(t3)               # out[i] = q_byte (low 8 bits)
  addi t1, t1, 1
  j .Lu256d_loop
.Lu256d_done:
  mv a0, t0                  # remainder
  ret
