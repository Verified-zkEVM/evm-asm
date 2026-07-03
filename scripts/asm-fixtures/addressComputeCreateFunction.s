address_compute_create:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # sender ptr
  mv s1, a1                   # nonce
  mv s2, a2                   # output ptr
  la t0, ac_buffer
  li t1, 0x94
  sb t1, 1(t0)
  ld t1,  0(s0); sd t1,  2(t0)
  ld t1,  8(s0); sd t1, 10(t0)
  lwu t1, 16(s0); sw t1, 18(t0)
  beqz s1, .Lac_nonce_zero
  li t1, 128
  bgeu s1, t1, .Lac_nonce_long
  # nonce in 1..127: single byte = nonce.
  sb s1, 22(t0)
  li t2, 1
  j .Lac_have_nonce_len
.Lac_nonce_zero:
  li t1, 0x80
  sb t1, 22(t0)
  li t2, 1
  j .Lac_have_nonce_len
.Lac_nonce_long:
  la t3, ac_nonce_be
  srli t4, s1, 56; sb t4, 0(t3)
  srli t4, s1, 48; sb t4, 1(t3)
  srli t4, s1, 40; sb t4, 2(t3)
  srli t4, s1, 32; sb t4, 3(t3)
  srli t4, s1, 24; sb t4, 4(t3)
  srli t4, s1, 16; sb t4, 5(t3)
  srli t4, s1,  8; sb t4, 6(t3)
  sb s1, 7(t3)
  li t4, 0                    # leading zero count
.Lac_find_nz:
  add t5, t3, t4
  lbu t6, 0(t5)
  bnez t6, .Lac_found
  addi t4, t4, 1
  j .Lac_find_nz
.Lac_found:
  li t5, 8
  sub t2, t5, t4
  # Write prefix byte 0x80 + byte_count at offset 22.
  addi t5, t2, 0x80
  sb t5, 22(t0)
  addi t6, t0, 23             # dst cursor
  add t5, t3, t4              # src cursor
  mv t1, t2                   # remaining
.Lac_copy_nz:
  beqz t1, .Lac_have_nonce_len_pp
  lbu t4, 0(t5)
  sb t4, 0(t6)
  addi t5, t5, 1
  addi t6, t6, 1
  addi t1, t1, -1
  j .Lac_copy_nz
.Lac_have_nonce_len_pp:
  # In the long path, t2 = data byte count. Add 1 for the prefix.
  addi t2, t2, 1
.Lac_have_nonce_len:
  # payload_len = 21 (sender_rlp) + nonce_rlp_len (t2)
  addi t1, t2, 21
  # list prefix = 0xc0 + payload_len
  addi t3, t1, 0xc0
  sb t3, 0(t0)
  # Total length = 1 + payload_len = 22 + nonce_rlp_len.
  addi a1, t2, 22
  mv a0, t0
  la a2, ac_digest
  jal ra, zkvm_keccak256
  la t0, ac_digest
  ld t1, 12(t0); sd t1,  0(s2)
  ld t1, 20(t0); sd t1,  8(s2)
  lwu t1, 28(t0); sw t1, 16(s2)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
