zkvm_keccak256_segments:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                # &segments[0]
  mv s1, a1                # remaining segment count
  mv s2, a2                # output ptr
  la s3, zk3_state
  # zero state (25 × u64)
  mv t0, s3; li t1, 25
.Lkss_zero:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lkss_zero
  li s4, 0                 # rate-block fill (0..135), carried across segments
.Lkss_seg:
  beqz s1, .Lkss_pad
  ld s5, 0(s0)             # segment ptr
  ld s6, 8(s0)             # segment len
  addi s0, s0, 16
  addi s1, s1, -1
.Lkss_byte:
  beqz s6, .Lkss_seg
  lbu t0, 0(s5)            # message byte
  add t1, s3, s4           # &state[fill]
  lbu t2, 0(t1); xor t2, t2, t0; sb t2, 0(t1)
  addi s5, s5, 1; addi s6, s6, -1; addi s4, s4, 1
  li t0, 136; bne s4, t0, .Lkss_byte
  mv a0, s3
  .4byte 0x80052073        # keccak-f on full rate block
  li s4, 0
  j .Lkss_byte
.Lkss_pad:
  add t1, s3, s4
  lbu t2, 0(t1); xori t2, t2, 0x01; sb t2, 0(t1)   # pad start bit
  addi t1, s3, 135
  lbu t2, 0(t1); xori t2, t2, 0x80; sb t2, 0(t1)   # pad end bit
  mv a0, s3
  .4byte 0x80052073
  ld t0, 0(s3);  sd t0, 0(s2)
  ld t0, 8(s3);  sd t0, 8(s2)
  ld t0, 16(s3); sd t0, 16(s2)
  ld t0, 24(s3); sd t0, 24(s2)
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
