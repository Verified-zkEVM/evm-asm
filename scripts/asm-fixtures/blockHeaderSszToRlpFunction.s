block_header_ssz_to_rlp:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp)
  mv s0, a0                   # payload
  mv s1, a1                   # transactions_root
  mv s2, a2                   # withdrawals_root
  mv s3, a3                   # parent_beacon_block_root
  mv s4, a4                   # requests_hash
  mv s5, a5                   # out
  mv s6, a6                   # out_len
  mv s8, a7                   # block_access_list_hash
  li s7, 0                    # payload cursor
  addi a0, s0, 0; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  la a0, bhr_empty_ommers; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 32; li a1, 20
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 52; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  mv a0, s1; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 84; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 116; li a1, 256
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  la a0, bhr_zero8; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  addi a0, s0, 404; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  addi a0, s0, 412; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  addi a0, s0, 420; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  addi a0, s0, 428; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  lbu t0, 436(s0); lbu t1, 437(s0); slli t1, t1, 8; or t0, t0, t1
  lbu t1, 438(s0); slli t1, t1, 16; or t0, t0, t1
  lbu t1, 439(s0); slli t1, t1, 24; or t0, t0, t1   # extra_off
  lbu t2, 504(s0); lbu t1, 505(s0); slli t1, t1, 8; or t2, t2, t1
  lbu t1, 506(s0); slli t1, t1, 16; or t2, t2, t1
  lbu t1, 507(s0); slli t1, t1, 24; or t2, t2, t1   # tx_off
  sub a1, t2, t0              # extra_len
  add a0, s0, t0              # extra_ptr
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 372; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  la a0, bhr_zero8; li a1, 8
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 440; li a1, 32; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 32; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  mv a0, s2; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 512; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  addi a0, s0, 520; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  mv a0, s3; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  mv a0, s4; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  mv a0, s8; li a1, 32
  la a2, bhr_payload; add a2, a2, s7; la a3, bhr_flen
  jal ra, rlp_encode_bytes
  la t0, bhr_flen; ld t1, 0(t0); add s7, s7, t1
  addi a0, s0, 532; li a1, 8; la a2, bhr_uint_be
  jal ra, bhr_rev_le_be
  la a0, bhr_uint_be; li a1, 8; la a2, bhr_payload; add a2, a2, s7
  jal ra, rlp_encode_uint_be
  add s7, s7, a0
  mv a0, s7; mv a1, s5; la a2, bhr_prefix_len
  jal ra, rlp_encode_list_prefix
  la t0, bhr_prefix_len; ld t1, 0(t0)
  add t2, s5, t1              # dst = out + prefix_len
  la t3, bhr_payload          # src
  mv t4, s7                   # remaining
.Lbhr_cp:
  beqz t4, .Lbhr_cpd
  lbu t5, 0(t3); sb t5, 0(t2)
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1
  j .Lbhr_cp
.Lbhr_cpd:
  add t1, t1, s7              # out_len = prefix_len + payload_len
  sd t1, 0(s6)
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp)
  addi sp, sp, 96
  ret
