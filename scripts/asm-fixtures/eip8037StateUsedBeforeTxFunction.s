eip8037_state_used_before_tx:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)
  mv s0, a0                   # BAL ptr
  mv s1, a1                   # BAL len
  mv s2, a2                   # target tx index (1-based)
  mv s3, a3                   # out ptr
  sd zero, 0(s3)
  mv a0, s0; mv a1, s1; la a2, bsg_count
  jal ra, rlp_list_count_items
  bnez a0, .Lesub_ok
  la t0, bsg_count; ld s4, 0(t0)        # account count
  li s5, 0                              # account i
.Lesub_acct_loop:
  beq s5, s4, .Lesub_ok
  mv a0, s0; mv a1, s1; mv a2, s5; la a3, bsg_off; la a4, bsg_len
  jal ra, rlp_item_span
  bnez a0, .Lesub_ok
  la t0, bsg_off; ld t1, 0(t0); add s6, s0, t1     # account ptr
  la t0, bsg_len; ld s7, 0(t0)                     # account len
  mv a0, s6; mv a1, s7; li a2, 1; la a3, bsg_off; la a4, bsg_len
  jal ra, rlp_item_span                              # storage_changes list
  bnez a0, .Lesub_next_acct
  la t0, bsg_off; ld t1, 0(t0); add s8, s6, t1      # storage_changes ptr
  la t0, bsg_len; ld s9, 0(t0)                      # storage_changes len
  mv a0, s8; mv a1, s9; la a2, bsg_slot_count
  jal ra, rlp_list_count_items
  bnez a0, .Lesub_next_acct
  la t0, bsg_slot_count; ld s10, 0(t0)
  li s6, 0                                          # slot i
.Lesub_slot_loop:
  beq s6, s10, .Lesub_next_acct
  mv a0, s8; mv a1, s9; mv a2, s6; la a3, bsg_slot_off; la a4, bsg_slot_len
  jal ra, rlp_item_span
  bnez a0, .Lesub_next_slot
  la t0, bsg_slot_off; ld t1, 0(t0); add t2, s8, t1 # slot-change ptr
  la t0, bsg_slot_len; ld t3, 0(t0)                 # slot-change len
  la t0, bsg_slot_ptr; sd t2, 0(t0); la t0, bsg_slot_item_len; sd t3, 0(t0)
  mv a0, t2; mv a1, t3; li a2, 1; la a3, bsg_changes_off; la a4, bsg_changes_len
  jal ra, rlp_item_span                              # per-slot changes list
  bnez a0, .Lesub_next_slot
  la t0, bsg_slot_ptr; ld t2, 0(t0); la t0, bsg_changes_off; ld t1, 0(t0); add t2, t2, t1
  la t0, bsg_changes_ptr; sd t2, 0(t0)
  la t0, bsg_changes_len; ld t3, 0(t0)
  mv a0, t2; mv a1, t3; la a2, bsg_change_count
  jal ra, rlp_list_count_items
  bnez a0, .Lesub_next_slot
  la t0, bsg_change_count; ld t4, 0(t0); beqz t4, .Lesub_next_slot
  addi t4, t4, -1                                  # final change only
  la t0, bsg_changes_ptr; ld a0, 0(t0); la t0, bsg_changes_len; ld a1, 0(t0); mv a2, t4; la a3, bsg_change_off; la a4, bsg_change_len
  jal ra, rlp_item_span
  bnez a0, .Lesub_next_slot
  la t0, bsg_changes_ptr; ld t2, 0(t0); la t0, bsg_change_off; ld t1, 0(t0); add t2, t2, t1
  la t0, bsg_change_len; ld t3, 0(t0)
  la t0, bsg_change_ptr; sd t2, 0(t0); la t0, bsg_change_item_len; sd t3, 0(t0)
  mv a0, t2; mv a1, t3; li a2, 0; la a3, bsg_idx_off; la a4, bsg_idx_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lesub_next_slot
  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 0; la a3, bsg_index
  jal ra, rlp_field_to_u64
  bnez a0, .Lesub_next_slot
  la t0, bsg_index; ld t1, 0(t0)
  beqz t1, .Lesub_next_slot                         # system writes do not spend tx state gas
  bgeu t1, s2, .Lesub_next_slot
  la t0, bsg_change_ptr; ld a0, 0(t0); la t0, bsg_change_item_len; ld a1, 0(t0); li a2, 1; la a3, bsg_value_off; la a4, bsg_value_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lesub_next_slot
  la t0, bsg_value_len; ld t1, 0(t0); beqz t1, .Lesub_next_slot
  ld t2, 0(s3)
  li t3, 97920
  add t2, t2, t3; sd t2, 0(s3)
.Lesub_next_slot:
  addi s6, s6, 1; j .Lesub_slot_loop
.Lesub_next_acct:
  addi s5, s5, 1; j .Lesub_acct_loop
.Lesub_ok:
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)
  addi sp, sp, 96
  ret
