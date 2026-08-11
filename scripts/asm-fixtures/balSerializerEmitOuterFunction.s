bal_serializer_emit_outer:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0; mv s1, a1
  jal ra, bal_serializer_measure_outer
  mv a0, s0; la t0, bal_serializer_outer_payload; ld a1, 0(t0); mv a2, s1
  jal ra, bal_rlp_emit_list_header
  la t0, bal_builder_account_count; ld s2, 0(t0)
  li s3, 0
.Lbseo_loop:
  bgeu s3, s2, .Lbseo_done
  li t0, 24; mul t1, s3, t0; la t2, bal_builder_accounts; add t3, t2, t1
  sd t3, 40(sp)
  mv a0, t3; jal ra, bal_serializer_measure_account
  ld t3, 40(sp); mv a0, s0; mv a1, t3; mv a2, s1
  jal ra, bal_serializer_emit_account
  addi s3, s3, 1; j .Lbseo_loop
.Lbseo_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
