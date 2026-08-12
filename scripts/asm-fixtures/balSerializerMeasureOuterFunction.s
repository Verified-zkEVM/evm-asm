bal_serializer_measure_outer:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  la t0, bal_builder_account_count; ld s1, 0(t0)
  li s2, 0
  li s3, 0
.Lbsmo_loop:
  bgeu s3, s1, .Lbsmo_done
  li t0, 24; mul t1, s3, t0; la t2, bal_builder_accounts; add s0, t2, t1
  mv a0, s0; jal ra, bal_serializer_measure_account
  mv t5, a0
  jal ra, bal_rlp_list_header_len
  add s2, s2, t5; add s2, s2, a0
  addi s3, s3, 1; j .Lbsmo_loop
.Lbsmo_done:
  la t0, bal_serializer_outer_payload; sd s2, 0(t0)
  mv a0, s2
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
