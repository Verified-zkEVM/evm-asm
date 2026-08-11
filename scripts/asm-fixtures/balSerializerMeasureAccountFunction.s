bal_serializer_measure_account:
  addi sp, sp, -48; sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0; li s1, 0
  addi s1, s1, 21
  mv a0, s0; jal ra, bal_serializer_measure_storage
  mv a0, a0; jal ra, bal_rlp_list_header_len
  la t0, bal_serializer_len_table; ld t1, 8(t0); add s1, s1, t1; add s1, s1, a0
  mv a0, s0; jal ra, bal_serializer_measure_reads
  jal ra, bal_rlp_list_header_len
  la t0, bal_serializer_len_table; ld t1, 16(t0); add s1, s1, t1; add s1, s1, a0
  mv a0, s0; jal ra, bal_serializer_measure_balance
  jal ra, bal_rlp_list_header_len
  la t0, bal_serializer_len_table; ld t1, 24(t0); add s1, s1, t1; add s1, s1, a0
  mv a0, s0; jal ra, bal_serializer_measure_nonce
  jal ra, bal_rlp_list_header_len
  la t0, bal_serializer_len_table; ld t1, 32(t0); add s1, s1, t1; add s1, s1, a0
  mv a0, s0; jal ra, bal_serializer_measure_code
  jal ra, bal_rlp_list_header_len
  la t0, bal_serializer_len_table; ld t1, 40(t0); add s1, s1, t1; add s1, s1, a0
  la t0, bal_serializer_len_table; sd s1, 0(t0)
  mv a0, s1
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 48
  ret
