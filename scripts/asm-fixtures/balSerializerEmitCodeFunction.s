bal_serializer_emit_code:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la t0, bal_builder_code_count; ld s3, 0(t0)
  li s4, 0
.Lbsec_loop:
  bgeu s4, s3, .Lbsec_done
  slli t1, s4, 6; la t2, bal_builder_code_changes; add t3, t2, t1; sd t3, 48(sp)
  mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsec_next
  ld t3, 48(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 56(sp)
  la a0, bal_serializer_throwaway_ctx; la a1, bal_rlp_emit_bytes
  ld t3, 48(sp); ld a2, 32(t3); ld a3, 40(t3); la a4, bal_serializer_hdr_scratch
  jal ra, bal_rlp_measure_into_throwaway
  ld t4, 56(sp); add t4, t4, a0; sd t4, 56(sp)
  mv a0, s0; ld a1, 56(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header
  la t0, bv_bal_shadow_emit_code_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar
  ld t3, 48(sp); mv a0, s0; ld a1, 32(t3); ld a2, 40(t3)
  la a3, bal_serializer_hdr_scratch; jal ra, bal_rlp_emit_bytes
.Lbsec_next:
  addi s4, s4, 1; j .Lbsec_loop
.Lbsec_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 80
  ret
