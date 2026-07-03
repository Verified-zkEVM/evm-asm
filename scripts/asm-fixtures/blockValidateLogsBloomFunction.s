block_validate_logs_bloom:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                   # header_rlp ptr
  mv s1, a1                   # header_rlp len
  mv s2, a2                   # receipts list ptr
  mv s3, a3                   # receipts list len
  mv s4, a4                   # is_valid out
  # ---- Extract header.logs_bloom into bvlb_header_bloom ----
  mv a0, s0; mv a1, s1
  la a2, bvlb_header_bloom
  jal ra, header_extract_logs_bloom
  bnez a0, .Lbvlb_header_fail
  # ---- Zero bvlb_computed_bloom (256 B) ----
  la t0, bvlb_computed_bloom
  li t1, 32
.Lbvlb_zero:
  beqz t1, .Lbvlb_zero_done
  sd zero, 0(t0)
  addi t0, t0, 8
  addi t1, t1, -1
  j .Lbvlb_zero
.Lbvlb_zero_done:
  # ---- Compute block bloom from receipts list ----
  mv a0, s2; mv a1, s3
  la a2, bvlb_computed_bloom
  jal ra, block_logs_bloom_from_receipts_list
  bnez a0, .Lbvlb_receipts_fail
  # ---- Compare the two blooms ----
  la a0, bvlb_header_bloom
  la a1, bvlb_computed_bloom
  mv a2, s4
  jal ra, bloom_eq
  li a0, 0
  j .Lbvlb_ret
.Lbvlb_header_fail:
  sd zero, 0(s4)
  li a0, 1
  j .Lbvlb_ret
.Lbvlb_receipts_fail:
  sd zero, 0(s4)
  li a0, 2
.Lbvlb_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
