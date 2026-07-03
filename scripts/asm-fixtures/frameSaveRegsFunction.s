frame_save_regs:
  la t0, frame_save_area
  slli t1, a0, 4                 # depth*16
  add t0, t0, t1
  sd a1, 0(t0)                   # saved pc
  sd a2, 8(t0)                   # saved codebase
  ret
