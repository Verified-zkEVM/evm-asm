u256_eq:
  li t0, 0                   # byte index
  li t6, 32
.Lu256eq_loop:
  beq t0, t6, .Lu256eq_yes   # 32 bytes equal → a == b
  add t1, a0, t0
  add t2, a1, t0
  lbu t3, 0(t1)
  lbu t4, 0(t2)
  bne t3, t4, .Lu256eq_no
  addi t0, t0, 1
  j .Lu256eq_loop
.Lu256eq_yes:
  li a0, 1
  ret
.Lu256eq_no:
  li a0, 0
  ret
