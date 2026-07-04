frame_depth_pop:
  la t0, evm_call_depth
  ld a0, 0(t0)
  addi a0, a0, -1
  sd a0, 0(t0)
  ret
