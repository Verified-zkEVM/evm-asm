ssz_withdrawal_to_rlp:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                   # ssz withdrawal
  mv s1, a1                   # out
  mv s2, a2                   # out_len
  li s3, 0                    # payload cursor
  # field 0: index (u64 LE @0)
  addi a0, s0, 0; li a1, 8; la a2, swr_be
  jal ra, swr_rev_le_be
  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3
  jal ra, rlp_encode_uint_be
  add s3, s3, a0
  # field 1: validator_index (u64 LE @8)
  addi a0, s0, 8; li a1, 8; la a2, swr_be
  jal ra, swr_rev_le_be
  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3
  jal ra, rlp_encode_uint_be
  add s3, s3, a0
  # field 2: address (20 B @16)
  addi a0, s0, 16; li a1, 20
  la a2, swr_payload; add a2, a2, s3; la a3, swr_flen
  jal ra, rlp_encode_bytes
  la t0, swr_flen; ld t1, 0(t0); add s3, s3, t1
  # field 3: amount (u64 LE @36)
  addi a0, s0, 36; li a1, 8; la a2, swr_be
  jal ra, swr_rev_le_be
  la a0, swr_be; li a1, 8; la a2, swr_payload; add a2, a2, s3
  jal ra, rlp_encode_uint_be
  add s3, s3, a0
  # list prefix + copy payload after it
  mv a0, s3; mv a1, s1; la a2, swr_prefix_len
  jal ra, rlp_encode_list_prefix
  la t0, swr_prefix_len; ld t1, 0(t0)
  add t2, s1, t1; la t3, swr_payload; mv t4, s3
.Lswr_cp:
  beqz t4, .Lswr_cpd
  lbu t5, 0(t3); sb t5, 0(t2)
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1
  j .Lswr_cp
.Lswr_cpd:
  add t1, t1, s3; sd t1, 0(s2)
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
