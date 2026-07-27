header_validate_post_merge:
  addi sp, sp, -40
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0
  mv s1, a1
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lhvpm_parse
  mv s2, a0
  mv s3, a1
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next
  bnez a1, .Lhvpm_parse
  mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next
  bnez a1, .Lhvpm_parse
  li t0, 32
  bne a2, t0, .Lhvpm_ommers
  sub t1, a0, a2
  la t0, empty_ommers_hash
  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lhvpm_ommers
  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lhvpm_ommers
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lhvpm_ommers
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lhvpm_ommers
  mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next
  bnez a1, .Lhvpm_parse
  bnez a2, .Lhvpm_difficulty
  mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next; bnez a1, .Lhvpm_parse; mv s2, a0
  mv a0, s2; mv a1, s3; jal ra, rlp_walk_next
  bnez a1, .Lhvpm_parse
  li t0, 8
  bne a2, t0, .Lhvpm_nonce
  sub t1, a0, a2
  ld t2, 0(t1)
  bnez t2, .Lhvpm_nonce
  li a0, 0
  j .Lhvpm_ret
.Lhvpm_ommers:
  li a0, 1
  j .Lhvpm_ret
.Lhvpm_difficulty:
  li a0, 2
  j .Lhvpm_ret
.Lhvpm_nonce:
  li a0, 3
  j .Lhvpm_ret
.Lhvpm_parse:
  li a0, 4
.Lhvpm_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 40
  ret
