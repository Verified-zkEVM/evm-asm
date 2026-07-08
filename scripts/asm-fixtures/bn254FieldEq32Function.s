bnf_eq32:
  li x5, 32
  mv x6, x10
  mv x7, x11
  beq x5, x0, .+32
  lbu x28, 0(x6)
  lbu x29, 0(x7)
  bne x28, x29, .+20
  addi x6, x6, 1
  addi x7, x7, 1
  addi x5, x5, -1
  jal x0, .-28
  li x10, 1
  beq x5, x0, .+8
  li x10, 0
  jalr x0, 0(x1)
