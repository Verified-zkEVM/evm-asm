bal_serializer_measure_balance:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0
  la t0, bal_builder_balance_count; ld s1, 0(t0)
  li s2, 0
  li s3, 0
.Lbsmb_loop:
  bgeu s3, s1, .Lbsmb_done
  li t0, 64; mul t1, s3, t0; la t2, bal_builder_balance_changes; add s4, t2, t1
  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsmb_next
  ld a1, 24(s4); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0
  addi a0, s4, 32; jal ra, bal_serializer_balance_to_le
  la a0, bal_serializer_balance_le; jal ra, bal_rlp_scalar_rlp_len; add t5, t5, a0
  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0
  add s2, s2, t5
.Lbsmb_next:
  addi s3, s3, 1; j .Lbsmb_loop
.Lbsmb_done:
  la t0, bal_serializer_len_table; sd s2, 24(t0)
  mv a0, s2
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 80
  ret
