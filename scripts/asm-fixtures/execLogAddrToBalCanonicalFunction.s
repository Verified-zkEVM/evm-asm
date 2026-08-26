exec_log_addr_to_bal_canonical:
  li x5, 0
  li x6, 20
  beq x5, x6, .+36
  li x7, 19
  sub x7, x7, x5
  add x7, x10, x7
  lbu x28, 0(x7)
  add x29, x11, x5
  sb x28, 0(x29)
  addi x5, x5, 1
  jal x0, .-36
  jalr x0, 0(x1)
