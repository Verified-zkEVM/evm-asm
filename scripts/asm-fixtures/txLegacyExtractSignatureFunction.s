tx_legacy_extract_signature:
  addi sp, sp, -80
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0                   # tx_rlp ptr
  mv s1, a1                   # tx_rlp len
  mv s2, a2                   # y_parity/v out
  mv s3, a3                   # r out (32 B)
  mv s4, a4                   # s out (32 B)
  mv a0, s0; mv a1, s1
  jal ra, rlp_walk_init
  bnez a2, .Ltlxs_fail
  mv s5, a0                   # cursor
  mv s6, a1                   # end
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail; mv s5, a0
  # ---- Signature field 0: y_parity/v (canonical uint <= 8 bytes) -> u64 ----
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail
  sub t0, a0, a2; mv s7, a0; mv a0, t0; mv a1, a2
  jal ra, rlp_content_to_u64_strict
  bnez a1, .Ltlxs_size
  sd a0, 0(s2); mv s5, s7
  # ---- Signature field 1: r (canonical u256 BE <= 32 bytes) ----
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail
  sub t0, a0, a2; mv s7, a0; mv a0, t0; mv a1, a2; mv a2, s3
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Ltlxs_size
  mv s5, s7
  # ---- Signature field 2: s (canonical u256 BE <= 32 bytes) ----
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next; bnez a1, .Ltlxs_fail
  sub t0, a0, a2; mv a0, t0; mv a1, a2; mv a2, s4
  jal ra, rlp_content_to_u256_be_strict
  bnez a0, .Ltlxs_size
  li a0, 0
  j .Ltlxs_ret
.Ltlxs_fail:
  li a0, 1
  j .Ltlxs_ret
.Ltlxs_size:
  li a0, 2
.Ltlxs_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
