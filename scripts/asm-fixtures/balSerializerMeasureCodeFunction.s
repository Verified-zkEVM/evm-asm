bal_serializer_measure_code:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0
  la t0, bal_builder_code_count; ld s1, 0(t0)
  li s2, 0; li s3, 0
.Lbsmc_loop:
  bgeu s3, s1, .Lbsmc_done
  slli t1, s3, 6; la t2, bal_builder_code_changes; add s4, t2, t1
  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsmc_next
  ld a1, 24(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0
  sd t5, 48(sp)
  la a0, bal_serializer_throwaway_ctx
  la a1, bal_rlp_emit_bytes
  ld a2, 32(s4); ld a3, 40(s4); la a4, bal_serializer_hdr_scratch
  jal ra, bal_rlp_measure_into_throwaway
  ld t5, 48(sp)
  add t5, t5, a0
  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0
  add s2, s2, t5
.Lbsmc_next:
  addi s3, s3, 1; j .Lbsmc_loop
.Lbsmc_done:
  la t0, bal_serializer_len_table; sd s2, 40(t0)
  mv a0, s2
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 64
  ret
