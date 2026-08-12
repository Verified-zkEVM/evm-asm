bal_serializer_emit_storage:
  addi sp, sp, -112
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  la t0, bal_builder_storage_change_count; ld s3, 0(t0)
  li s4, 0
.Lbses_slot:
  bgeu s4, s3, .Lbses_done
  li t0, 96; mul t1, s4, t0; la t2, bal_builder_storage_changes; add s5, t2, t1
  mv a0, s1; mv a1, s5; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbses_slot_next
  mv a0, s1; mv a1, s5; mv a2, s4; jal ra, bal_serializer_slot_seen_before
  bnez a0, .Lbses_slot_next
  mv a0, s1; mv a1, s5; jal ra, bal_serializer_measure_slot
  mv s6, a0; mv s7, a1
  mv a0, s0; mv a1, s6; mv a2, s2; jal ra, bal_rlp_emit_list_header
  addi a0, s5, 32; jal ra, bal_serializer_slot_to_le
  mv a0, s0; la a1, bal_serializer_slot_le; mv a2, s2; jal ra, bal_rlp_emit_scalar
  mv a0, s0; mv a1, s7; mv a2, s2; jal ra, bal_rlp_emit_list_header
  li s8, 0
.Lbses_chg:
  bgeu s8, s3, .Lbses_chg_done
  li t0, 96; mul t1, s8, t0; la t2, bal_builder_storage_changes; add t3, t2, t1
  sd t3, 80(sp)
  mv a0, s1; mv a1, t3; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbses_chg_next
  ld t3, 80(sp); addi a0, s5, 32; addi a1, t3, 32; jal ra, bal_serializer_slot_eq
  beqz a0, .Lbses_chg_next
  ld t3, 80(sp); ld a1, 24(t3); la a0, bal_serializer_u64_field
  jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; sd a0, 88(sp)
  ld t3, 80(sp); addi a0, t3, 64; jal ra, bal_rlp_scalar_rlp_len
  ld t4, 88(sp); add t4, t4, a0; sd t4, 88(sp)
  mv a0, s0; ld a1, 88(sp); mv a2, s2; jal ra, bal_rlp_emit_list_header
  la t0, bv_bal_shadow_emit_storage_changes; ld t1, 0(t0); addi t1, t1, 1; sd t1, 0(t0)
  mv a0, s0; la a1, bal_serializer_u64_field; mv a2, s2; jal ra, bal_rlp_emit_scalar
  ld t3, 80(sp); mv a0, s0; addi a1, t3, 64; mv a2, s2; jal ra, bal_rlp_emit_scalar
.Lbses_chg_next:
  addi s8, s8, 1; j .Lbses_chg
.Lbses_chg_done:
.Lbses_slot_next:
  addi s4, s4, 1; j .Lbses_slot
.Lbses_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 112
  ret
