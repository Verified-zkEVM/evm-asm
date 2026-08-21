rlp_validate_payload:
  addi x2, x2, -32
  sd x1, 0(x2)
  sd x13, 8(x2)
  beq x10, x11, .+44
  bgeu x10, x11, .+48
  mv x15, x10
  mv x16, x11
  li x12, 1024
  la x13, rlp_recursive_decode_frame
  jal x1, rlp_recursive_decode_items
  beq x10, x0, .+24
  li x10, 7
  jal x0, .+20
  li x10, 0
  jal x0, .+8
  li x10, 7
  ld x13, 8(x2)
  ld x1, 0(x2)
  addi x2, x2, 32
  jalr x0, 0(x1)
