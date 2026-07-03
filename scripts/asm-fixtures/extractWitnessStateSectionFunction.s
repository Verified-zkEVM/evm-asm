extract_witness_state_section:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # out state_ptr
  mv s2, a2                   # out state_len
  # witness = SSZ_BASE + outer.offsets[1] (u32 @ SSZ_BASE+4)
  addi a0, s0, 4
  jal ra, sws_u32le
  add s0, s0, a0              # s0 = witness addr (SSZ_BASE no longer needed)
  # state_off = u32 @ witness+0
  mv a0, s0
  jal ra, sws_u32le
  mv t4, a0                   # state_off (sws_u32le clobbers only t0/t1, so t4 survives)
  # codes_off = u32 @ witness+4
  addi a0, s0, 4
  jal ra, sws_u32le           # a0 = codes_off; t4 = state_off
  sub t5, a0, t4              # state_len = codes_off - state_off
  add t6, s0, t4              # state_ptr = witness + state_off
  sd t6, 0(s1)
  sd t5, 0(s2)
  li a0, 0
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
