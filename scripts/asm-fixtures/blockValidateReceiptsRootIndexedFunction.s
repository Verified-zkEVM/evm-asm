block_validate_receipts_root_indexed:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp)
  mv s0, a0                   # header_rlp ptr
  mv s1, a1                   # header_rlp len
  mv s2, a2                   # value descriptors
  mv s3, a3                   # n receipts
  # ---- Extract header.receipts_root (field 5) ----
  mv a0, s0; mv a1, s1; la a2, bvrri_expected_root
  jal ra, header_extract_receipts_root
  bnez a0, .Lbvrri_header_fail
  # ---- Compute indexed receipts trie root ----
  mv a0, s2; mv a1, s3; la a2, bvrri_computed_root
  jal ra, mpt_indexed_trie_root_small
  bnez a0, .Lbvrri_trie_fail
  la t0, bvrri_expected_root
  la t1, bvrri_computed_root
  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lbvrri_neq
  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lbvrri_neq
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lbvrri_neq
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lbvrri_neq
  li a0, 0
  li a1, 1
  j .Lbvrri_ret
.Lbvrri_neq:
  li a0, 0
  li a1, 0
  j .Lbvrri_ret
.Lbvrri_header_fail:
  li a1, 0
  j .Lbvrri_ret
.Lbvrri_trie_fail:
  li a0, 3
  li a1, 0
.Lbvrri_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp)
  addi sp, sp, 48
  ret
