chain_extract_first_last_block_hash:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  beqz s0, .Lceflbh_empty
  # first = keccak256(headers[0])
  ld a1, 0(s1)
  mv a0, s2
  mv a2, s3
  jal ra, block_hash_from_header
  # Advance to last header
  mv t1, s2
  mv t2, s1
  addi t3, s0, -1
.Lceflbh_skip:
  beqz t3, .Lceflbh_at_last
  ld t4, 0(t2)
  add t1, t1, t4
  addi t2, t2, 8
  addi t3, t3, -1
  j .Lceflbh_skip
.Lceflbh_at_last:
  ld a1, 0(t2)
  mv a0, t1
  mv a2, s4
  jal ra, block_hash_from_header
  li a0, 0
  j .Lceflbh_ret
.Lceflbh_empty:
  li a0, 1
.Lceflbh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
