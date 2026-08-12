bal_serializer_emit_account:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la t0, bal_serializer_len_table; ld a1, 0(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; li a2, 20; mv a3, s2; jal ra, bal_rlp_emit_bytes
  la t0, bal_serializer_len_table; ld a1, 8(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_storage
  la t0, bal_serializer_len_table; ld a1, 16(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_reads
  la t0, bal_serializer_len_table; ld a1, 24(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_balance
  la t0, bal_serializer_len_table; ld a1, 32(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_nonce
  la t0, bal_serializer_len_table; ld a1, 40(t0)
  mv a0, s0; mv a2, s2; jal ra, bal_rlp_emit_list_header
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, bal_serializer_emit_code
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 48
  ret
