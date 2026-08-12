bal_account_nonce_before_index:
  addi sp, sp, -112
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  li a2, 4; addi a3, sp, 72; addi a4, sp, 80
  jal ra, rlp_list_nth_item
  bnez a0, .Lbanbi_malformed
  ld t0, 72(sp); add s3, s0, t0; ld s4, 80(sp)
  mv a0, s3; mv a1, s4; addi a2, sp, 88; jal ra, rlp_list_count_items
  bnez a0, .Lbanbi_malformed
  ld s4, 88(sp); li s5, 0; li s6, 0; li s7, 0; sd zero, 104(sp)
.Lbanbi_loop:
  beq s5, s4, .Lbanbi_done_scan
  mv a0, s3; ld a1, 80(sp); mv a2, s5; addi a3, sp, 72; addi a4, sp, 88
  jal ra, rlp_item_span
  bnez a0, .Lbanbi_malformed
  ld t0, 72(sp); add t0, s3, t0; sd t0, 96(sp)
  mv a0, t0; ld a1, 88(sp); li a2, 0; addi a3, sp, 72; jal ra, rlp_field_to_u64_strict
  bnez a0, .Lbanbi_malformed
  ld t0, 72(sp); bgeu t0, s2, .Lbanbi_next
  bltu t0, s6, .Lbanbi_next
  mv s6, t0; ld a0, 96(sp); ld a1, 88(sp); li a2, 1; addi a3, sp, 72
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lbanbi_malformed
  ld s7, 72(sp); li t0, 1; sd t0, 104(sp)
.Lbanbi_next:
  addi s5, s5, 1; j .Lbanbi_loop
.Lbanbi_done_scan:
  ld t0, 104(sp); beqz t0, .Lbanbi_none
  li a0, 0; mv a1, s7; j .Lbanbi_return
.Lbanbi_none:
  li a0, 1; li a1, 0; j .Lbanbi_return
.Lbanbi_malformed:
  li a0, 2; li a1, 0
.Lbanbi_return:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 112; ret
