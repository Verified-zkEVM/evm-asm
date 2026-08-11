bal_serializer_emit_nonce:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la t0, bal_builder_nonce_count; ld s3, 0(t0)
  la t0, bald_non_builder_count; sd s3, 0(t0)
  li s4, 0
.Lbsen_loop:
  bgeu s4, s3, .Lbsen_done
  slli t1, s4, 5; slli t2, s4, 3; add t1, t1, t2
  la t2, bal_builder_nonce_changes; add t3, t2, t1; sd t3, 48(sp)
  la t0, bald_non_cmp_attempts; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  ld t3, 48(sp); mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsen_next
  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 56(sp)
  ld t3, 48(sp); ld a1, 32(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len
  ld t4, 56(sp); add t4, t4, a0; sd t4, 56(sp)
  mv a0, s0; ld a1, 56(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header
  la t0, bv_bal_shadow_emit_nonce_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar
  ld t3, 48(sp); ld a1, 32(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar
.Lbsen_next:
  addi s4, s4, 1; j .Lbsen_loop
.Lbsen_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 80
  ret
