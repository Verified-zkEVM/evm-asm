witness_headers_block_hash_at_index:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                  # section ptr
  mv s1, a1                  # section_len
  mv s2, a2                  # index
  mv s3, a3                  # out buf (32 B)
  sd zero,  0(s3); sd zero,  8(s3)
  sd zero, 16(s3); sd zero, 24(s3)
  beqz s1, .Lwhbh_oob
  lwu t0, 0(s0)
  srli s4, t0, 2             # s4 = N
  bgeu s2, s4, .Lwhbh_oob
  slli t0, s2, 2
  add t1, s0, t0
  lwu t2, 0(t1)
  add a0, s0, t2             # header_i start
  addi t3, s2, 1
  beq t3, s4, .Lwhbh_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4             # header_i end
  j .Lwhbh_have_end
.Lwhbh_use_end:
  add t4, s0, s1
.Lwhbh_have_end:
  sub a1, t4, a0             # header_i len
  mv a2, s3                  # out buf
  jal ra, zkvm_keccak256
  li a0, 0
  j .Lwhbh_ret
.Lwhbh_oob:
  li a0, 1
.Lwhbh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
