bal_serializer_measure_slot:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s4, 24(sp)
  sd s5, 32(sp); sd s6, 40(sp); sd s7, 48(sp)
  mv s0, a0; mv s4, a1
  la t0, bal_builder_storage_change_count; ld s1, 0(t0)
  li s5, 0
  li s6, 0
.Lbsmsl_chg:
  bgeu s6, s1, .Lbsmsl_chg_done
  li t0, 96; mul t1, s6, t0; la t2, bal_builder_storage_changes; add s7, t2, t1
  mv a0, s0; mv a1, s7; jal ra, bal_serializer_addr_matches_be
  beqz a0, .Lbsmsl_chg_next
  addi a0, s4, 32; addi a1, s7, 32; jal ra, bal_serializer_slot_eq
  beqz a0, .Lbsmsl_chg_next
  ld a1, 24(s7); la a0, bal_serializer_u64_field; jal ra, bal_serializer_u64_to_field
  la a0, bal_serializer_u64_field; jal ra, bal_rlp_scalar_rlp_len; mv t5, a0
  addi a0, s7, 64; jal ra, bal_rlp_scalar_rlp_len; add t5, t5, a0
  mv a0, t5; jal ra, bal_rlp_list_header_len; add t5, t5, a0
  add s5, s5, t5
.Lbsmsl_chg_next:
  addi s6, s6, 1; j .Lbsmsl_chg
.Lbsmsl_chg_done:
  mv s7, s5
  mv a0, s5; jal ra, bal_rlp_list_header_len; add s5, s5, a0
  addi a0, s4, 32; jal ra, bal_serializer_slot_to_le
  la a0, bal_serializer_slot_le; jal ra, bal_rlp_scalar_rlp_len; add s5, s5, a0
  mv a0, s5; mv a1, s7
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s4, 24(sp)
  ld s5, 32(sp); ld s6, 40(sp); ld s7, 48(sp)
  addi sp, sp, 64
  ret
