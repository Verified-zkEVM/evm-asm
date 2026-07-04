mpt_indexed_large_leaf_hash:
  addi sp, sp, -144
  sd ra,   0(sp)
  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)
  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)
  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s1, a0                   # value ptr
  mv s2, a1                   # value len
  mv s3, a2                   # path kind
  mv s4, a3                   # nibble for kind=1
  mv s5, a4                   # out hash
  li t0, 56
  bltu s2, t0, .Lillh_fail    # large-only: branch slots will use hash ref
  li t0, 1
  bgtu s3, t0, .Lillh_fail
  li t0, 15
  bgtu s4, t0, .Lillh_fail
  la s0, zk3_state
  mv t0, s0; li t1, 25
.Lillh_zero:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lillh_zero
  li s6, 0                    # current keccak rate offset
  li a0, 0x80
  mv a1, s2
  addi a2, sp, 104            # value prefix scratch
  jal ra, rlp_prefix_to_buffer
  mv s7, a0                   # value prefix len
  add s8, s7, s2              # encoded value item len
  addi a1, s8, 1              # list payload: one-byte hp item + value item
  li a0, 0xc0
  addi a2, sp, 120            # list prefix scratch
  jal ra, rlp_prefix_to_buffer
  mv s9, a0                   # list prefix len
  addi t0, sp, 136            # hp item scratch
  beqz s3, .Lillh_hp_empty
  ori t1, s4, 0x30
  j .Lillh_hp_store
.Lillh_hp_empty:
  li t1, 0x20
.Lillh_hp_store:
  sb t1, 0(t0)
  addi a0, sp, 120; mv a1, s9; jal ra, .Lillh_absorb
  addi a0, sp, 136; li a1, 1; jal ra, .Lillh_absorb
  addi a0, sp, 104; mv a1, s7; jal ra, .Lillh_absorb
  mv a0, s1; mv a1, s2; jal ra, .Lillh_absorb
  add t0, s0, s6
  lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0)
  addi t0, s0, 135
  lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0)
  mv a0, s0
  .4byte 0x80052073
  ld t0,  0(s0); sd t0,  0(s5)
  ld t0,  8(s0); sd t0,  8(s5)
  ld t0, 16(s0); sd t0, 16(s5)
  ld t0, 24(s0); sd t0, 24(s5)
  li a0, 0
  j .Lillh_ret
.Lillh_fail:
  li a0, 1
.Lillh_ret:
  ld ra,   0(sp)
  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)
  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)
  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 144
  ret
.Lillh_absorb:
  mv s10, a0
  mv s11, a1
.Lillh_absorb_loop:
  beqz s11, .Lillh_absorb_ret
  lbu t0, 0(s10)
  add t1, s0, s6
  lbu t2, 0(t1)
  xor t2, t2, t0
  sb t2, 0(t1)
  addi s10, s10, 1
  addi s11, s11, -1
  addi s6, s6, 1
  li t3, 136
  bne s6, t3, .Lillh_absorb_loop
  mv a0, s0
  .4byte 0x80052073
  li s6, 0
  j .Lillh_absorb_loop
.Lillh_absorb_ret:
  ret
