bal_serializer_measure_storage:
  addi sp, sp, -96
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0
  la t0, bal_builder_storage_change_count; ld s1, 0(t0)
  li s2, 0
  li s3, 0
.Lbsms_slot:
  bgeu s3, s1, .Lbsms_done
  li t0, 96; mul t1, s3, t0; la t2, bal_builder_storage_changes; add s4, t2, t1
  mv a0, s0; mv a1, s4; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsms_slot_next
  mv a0, s0; mv a1, s4; mv a2, s3; jal ra, bal_serializer_slot_seen_before
  bnez a0, .Lbsms_slot_next
  mv a0, s0; mv a1, s4; jal ra, bal_serializer_measure_slot
  mv s5, a0
  mv a0, s5; jal ra, bal_rlp_list_header_len; add s5, s5, a0
  add s2, s2, s5
.Lbsms_slot_next:
  addi s3, s3, 1; j .Lbsms_slot
.Lbsms_done:
  la t0, bal_serializer_len_table; sd s2, 8(t0)
  mv a0, s2
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 96
  ret
