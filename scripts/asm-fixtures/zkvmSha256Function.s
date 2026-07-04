zkvm_sha256:
  # save callee-saved regs (s0..s5)
  addi sp, sp, -48
  sd s0, 0(sp)
  sd s1, 8(sp)
  sd s2, 16(sp)
  sd s3, 24(sp)
  sd s4, 32(sp)
  sd s5, 40(sp)
  # s0 = state ptr; s1 = data ptr; s2 = remaining len;
  # s3 = output ptr (= caller's a2); s4 = bit-length;
  # s5 = sha256_input buffer base.
  la s0, sha256_w_state
  mv s1, a0
  mv s2, a1
  mv s3, a2
  slli s4, a1, 3
  la s5, sha256_w_input
  # initialise state from IV (LE-u32 packed, 4 × u64)
  la t0, sha256_w_iv
  ld t1, 0(t0);  sd t1, 0(s0)
  ld t1, 8(t0);  sd t1, 8(s0)
  ld t1, 16(t0); sd t1, 16(s0)
  ld t1, 24(t0); sd t1, 24(s0)
  # absorb full 64-byte blocks
.Lzkv_sha_loop:
  li t0, 64
  blt s2, t0, .Lzkv_sha_final
  ld t0, 0(s1);  sd t0, 0(s5)
  ld t0, 8(s1);  sd t0, 8(s5)
  ld t0, 16(s1); sd t0, 16(s5)
  ld t0, 24(s1); sd t0, 24(s5)
  ld t0, 32(s1); sd t0, 32(s5)
  ld t0, 40(s1); sd t0, 40(s5)
  ld t0, 48(s1); sd t0, 48(s5)
  ld t0, 56(s1); sd t0, 56(s5)
  la a0, sha256_w_params
  .4byte 0x80552073           # csrs 0x805, a0
  addi s1, s1, 64
  addi s2, s2, -64
  j .Lzkv_sha_loop
.Lzkv_sha_final:
  # zero the input buffer
  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)
  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)
  # byte-copy remaining s2 bytes from s1 to s5
  mv t0, s5
  mv t1, s1
  mv t2, s2
.Lzkv_sha_bcopy:
  beqz t2, .Lzkv_sha_pad
  lbu t3, 0(t1)
  sb  t3, 0(t0)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lzkv_sha_bcopy
.Lzkv_sha_pad:
  # write 0x80 at offset s2 in input buffer
  add t0, s5, s2
  li  t1, 0x80
  sb  t1, 0(t0)
  # if remainder < 56: single final block; else two-block path
  li  t0, 56
  blt s2, t0, .Lzkv_sha_writelen
  # two-block: compress this block (data + 0x80, no length yet)
  la  a0, sha256_w_params
  .4byte 0x80552073
  # zero input buffer for the second (length-only) block
  sd zero, 0(s5);  sd zero, 8(s5);  sd zero, 16(s5); sd zero, 24(s5)
  sd zero, 32(s5); sd zero, 40(s5); sd zero, 48(s5); sd zero, 56(s5)
.Lzkv_sha_writelen:
  # 8-byte BE bit-length at offset 56..64 of input buffer
  addi t0, s5, 56
  srli t1, s4, 56; sb t1, 0(t0)
  srli t1, s4, 48; sb t1, 1(t0)
  srli t1, s4, 40; sb t1, 2(t0)
  srli t1, s4, 32; sb t1, 3(t0)
  srli t1, s4, 24; sb t1, 4(t0)
  srli t1, s4, 16; sb t1, 5(t0)
  srli t1, s4,  8; sb t1, 6(t0)
  sb   s4, 7(t0)
  # compress final block
  la  a0, sha256_w_params
  .4byte 0x80552073
  # squeeze: byte-swap each u32 of state into output
  # output[i] = state[i ^ 3]   (reverses bytes within each 4-byte group)
  li  t0, 0
.Lzkv_sha_squeeze:
  li  t1, 32
  beq t0, t1, .Lzkv_sha_return
  xori t2, t0, 3
  add t3, s0, t2
  lbu t4, 0(t3)
  add t5, s3, t0
  sb  t4, 0(t5)
  addi t0, t0, 1
  j .Lzkv_sha_squeeze
.Lzkv_sha_return:
  li  a0, 0
  ld s0, 0(sp); ld s1, 8(sp); ld s2, 16(sp); ld s3, 24(sp); ld s4, 32(sp); ld s5, 40(sp)
  addi sp, sp, 48
  ret
