call_extra_gas:
  addi x5, x0, 100
  beq x10, x0, .+12
  lui x5, 0x1
  addiw x5, x5, -1496
  beq x11, x0, .+16
  lui x6, 0x2
  addiw x6, x6, 808
  add x5, x5, x6
  mv x10, x5
  jalr x0, 0(x1)
