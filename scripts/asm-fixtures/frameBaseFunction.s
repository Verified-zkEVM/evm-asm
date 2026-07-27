frame_base:
  addi t0, a0, -1                 # depth-1
  li t1, 0x19000                  # FRAME_STRIDE
  mul t0, t0, t1                  # (depth-1)*FRAME_STRIDE
  la t1, call_frame_arena
  add a0, t1, t0
  ret
