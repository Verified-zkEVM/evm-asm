rlp_validate_payload:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x10, 8(x2)
  sd x11, 16(x2)
  ld x10, 8(x2)
  ld x5, 16(x2)
  mv x11, x5
  beq x10, x5, .+32
  bltu x5, x10, .+44
  jal x1, rlp_walk_next_nested
  bne x11, x0, .+36
  ld x5, 16(x2)
  bltu x5, x10, .+28
  sd x10, 8(x2)
  jal x0, .-40
  li x10, 0
  ld x1, 0(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
  li x10, 7
  ld x1, 0(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
