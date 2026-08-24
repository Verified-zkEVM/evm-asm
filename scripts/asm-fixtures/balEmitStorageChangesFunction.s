bal_emit_storage_changes:
  addi sp, sp, -96
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  sd s7, 64(sp); sd s8, 72(sp); sd a0, 80(sp)
  la s0, tx_storage_writes_count; ld s1, 0(s0)
  li s2, 2731900608
  li s3, 0
.Lbesc_loop:
  bgeu s3, s1, .Lbesc_done
  slli s4, s3, 7; add s4, s2, s4
  la t0, storage_writes_count; ld t1, 0(t0)
  li t3, 2723367360; li t4, 0
  li s5, 0
.Lbesc_scan:
  bgeu t4, t1, .Lbesc_miss
  slli t2, t4, 7; add t5, t3, t2
  ld t2, 0(t5);  ld t6, 0(s4);  bne t2, t6, .Lbesc_next
  ld t2, 8(t5);  ld t6, 8(s4);  bne t2, t6, .Lbesc_next
  ld t2, 16(t5); ld t6, 16(s4); bne t2, t6, .Lbesc_next
  ld t2, 24(t5); ld t6, 24(s4); bne t2, t6, .Lbesc_next
  ld t2, 32(t5); ld t6, 32(s4); bne t2, t6, .Lbesc_next
  ld t2, 40(t5); ld t6, 40(s4); bne t2, t6, .Lbesc_next
  ld t2, 48(t5); ld t6, 48(s4); bne t2, t6, .Lbesc_next
  ld t2, 56(t5); ld t6, 56(s4); bne t2, t6, .Lbesc_next
  addi s5, t5, 64; j .Lbesc_have
.Lbesc_next:
  addi t4, t4, 1; j .Lbesc_scan
.Lbesc_miss:
  la t0, besc_addr_be; li t1, 20; addi t2, s4, 19
.Lbesc_arev:
  beqz t1, .Lbesc_arev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_arev
.Lbesc_arev_done:
  la t0, besc_slot_be; li t1, 32; addi t2, s4, 63
.Lbesc_srev:
  beqz t1, .Lbesc_srev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_srev
.Lbesc_srev_done:
  la t0, sv_pre_rlp_ptr; ld a0, 0(t0)
  la t0, sv_pre_rlp_len; ld a1, 0(t0)
  la a2, besc_addr_be; la a3, besc_slot_be
  la t0, bv_witness_state_ptr; ld a4, 0(t0); ld a6, 0(t0)
  la t0, bv_witness_state_len; ld a5, 0(t0); ld a7, 0(t0)
  jal ra, slot_at_header_state_root
  bnez a0, .Lbesc_zero_base
  la t0, besc_base_le; li t1, 32; la t2, sahsr_u256; addi t2, t2, 31
.Lbesc_brev:
  beqz t1, .Lbesc_brev_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_brev
.Lbesc_brev_done:
  la s5, besc_base_le; j .Lbesc_have
.Lbesc_zero_base:
  la t0, besc_base_le; sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)
  la s5, besc_base_le
.Lbesc_have:
  addi s6, s4, 64
  ld t2, 0(s5);  ld t6, 0(s6);  bne t2, t6, .Lbesc_emit
  ld t2, 8(s5);  ld t6, 8(s6);  bne t2, t6, .Lbesc_emit
  ld t2, 16(s5); ld t6, 16(s6); bne t2, t6, .Lbesc_emit
  ld t2, 24(s5); ld t6, 24(s6); bne t2, t6, .Lbesc_emit
  j .Lbesc_advance
.Lbesc_emit:
  la t0, besc_addr_be; li t1, 20; addi t2, s4, 19
.Lbesc_arev2:
  beqz t1, .Lbesc_arev2_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_arev2
.Lbesc_arev2_done:
  la t0, besc_slot_be; li t1, 32; addi t2, s4, 63
.Lbesc_srev2:
  beqz t1, .Lbesc_srev2_done; lbu t5, 0(t2); sb t5, 0(t0); addi t2, t2, -1; addi t0, t0, 1; addi t1, t1, -1; j .Lbesc_srev2
.Lbesc_srev2_done:
  la a0, besc_addr_be; ld a1, 80(sp); la a2, besc_slot_be; addi a3, s4, 64
  jal ra, bal_builder_record_storage_change
.Lbesc_advance:
  addi s3, s3, 1; j .Lbesc_loop
.Lbesc_done:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 96
  ret
