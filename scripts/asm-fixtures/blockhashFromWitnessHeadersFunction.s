blockhash_from_witness_headers:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s7, a0                  # target block number
  mv s0, a1                  # section ptr
  mv s1, a2                  # section_len
  mv s2, a3                  # block hash output ptr
  mv s3, a4                  # offset out ptr
  mv s4, a5                  # length out ptr
  beqz s1, .Lbhfwh_miss      # empty section ⇒ miss
  lwu t0, 0(s0)              # first inner offset = 4 * N
  srli s5, t0, 2             # s5 = N
  li s6, 0                   # s6 = i
.Lbhfwh_loop:
  beq s6, s5, .Lbhfwh_miss
  # Compute element i bounds.
  slli t0, s6, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add a0, s0, t2             # el_i_start
  addi t3, s6, 1
  beq t3, s5, .Lbhfwh_use_end
  slli t3, t3, 2             # 4*(i+1)
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # el_i_end
  j .Lbhfwh_have_end
.Lbhfwh_use_end:
  add t4, s0, s1             # el_i_end = section_end
.Lbhfwh_have_end:
  sub a1, t4, a0             # el_i_len
  la a2, bhfwh_number_buf
  jal ra, header_extract_number
  beqz a0, .Lbhfwh_compare
  li a0, 2                   # any header that fails to parse number ⇒ status 2
  j .Lbhfwh_ret
.Lbhfwh_compare:
  la t0, bhfwh_number_buf; ld t1, 0(t0)
  beq t1, s7, .Lbhfwh_match
  addi s6, s6, 1
  j .Lbhfwh_loop
.Lbhfwh_match:
  # Recompute (offset, length) since they were clobbered.
  slli t0, s6, 2
  add t1, s0, t0
  lwu t2, 0(t1)
  add a0, s0, t2             # el_start
  sd t2, 0(s3)               # *out_offset
  addi t3, s6, 1
  beq t3, s5, .Lbhfwh_last
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  sub t4, t4, t2             # length
  j .Lbhfwh_store_len
.Lbhfwh_last:
  sub t4, s1, t2
.Lbhfwh_store_len:
  sd t4, 0(s4)               # *out_length
  mv a1, t4                  # length argument for keccak
  mv a2, s2                  # block hash out ptr
  jal ra, zkvm_keccak256
  li a0, 0
  j .Lbhfwh_ret
.Lbhfwh_miss:
  li a0, 1
.Lbhfwh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
