frame_load_regs:
  la t0, frame_save_area
  slli t1, a0, 4
  add t0, t0, t1
  ld a0, 0(t0)                   # saved pc
  ld a1, 8(t0)                   # saved codebase
  ret
