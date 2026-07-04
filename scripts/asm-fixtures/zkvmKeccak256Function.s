zkvm_keccak256:
  # save s0/s1/s2/s4 (callee-saved per RV64 ABI)
  addi sp, sp, -32
  sd s0, 0(sp)
  sd s1, 8(sp)
  sd s2, 16(sp)
  sd s4, 24(sp)
  # stash args (a0/a1/a2 get clobbered during the absorb loop)
  mv s4, a0                # data ptr
  mv s1, a1                # remaining length
  mv s2, a2                # output ptr
  la s0, zk3_state
  # zero state (25 × u64)
  mv t3, s0
  li t4, 25
.Lzk3_zero:
  sd zero, 0(t3)
  addi t3, t3, 8
  addi t4, t4, -1
  bnez t4, .Lzk3_zero
  # absorb full blocks (rate = 136 bytes)
.Lzk3_full:
  li t4, 136
  blt s1, t4, .Lzk3_final
  mv t3, s0
  mv t5, s4
  li t6, 17
.Lzk3_xor:
  ld t0, 0(t5)
  ld t1, 0(t3)
  xor t1, t1, t0
  sd t1, 0(t3)
  addi t3, t3, 8
  addi t5, t5, 8
  addi t6, t6, -1
  bnez t6, .Lzk3_xor
  mv a0, s0
  .4byte 0x80052073
  addi s4, s4, 136
  addi s1, s1, -136
  j .Lzk3_full
.Lzk3_final:
  mv t3, s0
  mv t5, s4
  beqz s1, .Lzk3_pad
.Lzk3_bxor:
  lbu t0, 0(t5)
  lbu t1, 0(t3)
  xor t0, t0, t1
  sb t0, 0(t3)
  addi t3, t3, 1
  addi t5, t5, 1
  addi s1, s1, -1
  bnez s1, .Lzk3_bxor
.Lzk3_pad:
  lbu t0, 0(t3)
  xori t0, t0, 0x01
  sb t0, 0(t3)
  addi t3, s0, 135
  lbu t0, 0(t3)
  xori t0, t0, 0x80
  sb t0, 0(t3)
  mv a0, s0
  .4byte 0x80052073
  # squeeze 32 bytes to s2 (= output ptr)
  ld t0, 0(s0);  sd t0, 0(s2)
  ld t0, 8(s0);  sd t0, 8(s2)
  ld t0, 16(s0); sd t0, 16(s2)
  ld t0, 24(s0); sd t0, 24(s2)
  # return ZKVM_EOK
  li a0, 0
  ld s0, 0(sp)
  ld s1, 8(sp)
  ld s2, 16(sp)
  ld s4, 24(sp)
  addi sp, sp, 32
  ret
