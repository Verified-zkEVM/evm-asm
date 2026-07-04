header_validate_post_merge:
  addi sp, sp, -24
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a0                   # header ptr
  mv s1, a1                   # header_len
  # Check 1: field 1 (ommers_hash) == EMPTY_OMMERS_HASH.
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, hvpm_off; la a4, hvpm_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lhvpm_fail_parse
  la t0, hvpm_len; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lhvpm_fail_oh
  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3
  la t4, empty_ommers_hash
  ld t5,  0(t3); ld t6,  0(t4); bne t5, t6, .Lhvpm_fail_oh
  ld t5,  8(t3); ld t6,  8(t4); bne t5, t6, .Lhvpm_fail_oh
  ld t5, 16(t3); ld t6, 16(t4); bne t5, t6, .Lhvpm_fail_oh
  ld t5, 24(t3); ld t6, 24(t4); bne t5, t6, .Lhvpm_fail_oh
  # Check 2: field 7 (difficulty) is canonical-zero (len 0).
  mv a0, s0; mv a1, s1; li a2, 7
  la a3, hvpm_off; la a4, hvpm_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lhvpm_fail_parse
  la t0, hvpm_len; ld t1, 0(t0)
  bnez t1, .Lhvpm_fail_diff
  # Check 3: field 14 (nonce) is 8 zero bytes.
  mv a0, s0; mv a1, s1; li a2, 14
  la a3, hvpm_off; la a4, hvpm_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lhvpm_fail_parse
  la t0, hvpm_len; ld t1, 0(t0)
  li t2, 8
  bne t1, t2, .Lhvpm_fail_nonce
  la t0, hvpm_off; ld t3, 0(t0); add t3, s0, t3
  ld t5, 0(t3)
  bnez t5, .Lhvpm_fail_nonce
  li a0, 0
  j .Lhvpm_ret
.Lhvpm_fail_oh:
  li a0, 1
  j .Lhvpm_ret
.Lhvpm_fail_diff:
  li a0, 2
  j .Lhvpm_ret
.Lhvpm_fail_nonce:
  li a0, 3
  j .Lhvpm_ret
.Lhvpm_fail_parse:
  li a0, 4
.Lhvpm_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 24
  ret
