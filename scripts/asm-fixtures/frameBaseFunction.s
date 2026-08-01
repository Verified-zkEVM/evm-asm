frame_base:
  li t1, 0x19000                  # FRAME_STRIDE
  mul t0, a0, t1                  # depth*FRAME_STRIDE
  la t1, call_frame_arena
  add a0, t1, t0
  ret
