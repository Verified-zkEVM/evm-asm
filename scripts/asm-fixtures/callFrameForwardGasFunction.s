call_frame_forward_gas:
  srli x5, x10, 6
  sub x6, x10, x5
  bltu x11, x6, .+8
  jal x0, .+8
  mv x6, x11
  mv x11, x6
  beq x12, x0, .+16
  lui x5, 0x1
  addiw x5, x5, -1796
  add x6, x6, x5
  mv x10, x6
  jalr x0, 0(x1)
