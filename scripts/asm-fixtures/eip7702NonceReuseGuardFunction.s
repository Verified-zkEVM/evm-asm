eip7702_nonce_reuse_guard:
  addi sp, sp, -128
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # exec_payload
  mv s1, a1                   # SSZ_BASE
  mv s2, a2                   # BAL ptr
  mv s3, a3                   # BAL len
  addi a0, s0, 504; jal ra, enrg_u32le
  add s4, s0, a0              # tx list ptr
  addi a0, s0, 508; jal ra, enrg_u32le
  add t0, s0, a0              # withdrawals ptr
  bltu t0, s4, .Lenrg_ok
  sub s5, t0, s4              # tx list len
  beqz s5, .Lenrg_ok
  mv a0, s4; jal ra, enrg_u32le
  andi t0, a0, 3; bnez t0, .Lenrg_ok
  srli s6, a0, 2              # tx_count
  beqz s6, .Lenrg_ok
  li t0, 16; bgtu s6, t0, .Lenrg_ok
  addi a0, s1, 12; jal ra, enrg_u32le
  add s7, s1, a0              # public_keys ptr
  li s8, 0                    # tx index
.Lenrg_tx_loop:
  beq s8, s6, .Lenrg_ok
  slli t0, s8, 2; add t1, s4, t0; mv a0, t1; jal ra, enrg_u32le
  mv s9, a0                   # tx item offset
  addi t0, s8, 1
  beq t0, s6, .Lenrg_last_tx
  slli t1, t0, 2; add t1, s4, t1; mv a0, t1; jal ra, enrg_u32le
  j .Lenrg_have_next
.Lenrg_last_tx:
  mv a0, s5
.Lenrg_have_next:
  bltu a0, s9, .Lenrg_ok
  sub s10, a0, s9             # tx len
  add s9, s4, s9              # tx ptr
  mv a0, s9; mv a1, s10; la a2, enrg_tx_type; la a3, enrg_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Lenrg_next_tx
  la t0, enrg_tx_type; ld t1, 0(t0)
  la t0, enrg_inner_off; ld t2, 0(t0)
  add s11, s9, t2             # inner ptr
  bltu s10, t2, .Lenrg_next_tx
  sub t3, s10, t2             # inner len
  beqz t1, .Lenrg_legacy_nonce
  li t4, 4; bgtu t1, t4, .Lenrg_next_tx
  li a2, 1; j .Lenrg_read_nonce
.Lenrg_legacy_nonce:
  li a2, 0
.Lenrg_read_nonce:
  mv a0, s11; mv a1, t3; la a3, enrg_tx_nonce
  jal ra, rlp_field_to_u64
  bnez a0, .Lenrg_next_tx
  li t0, 65; mul t1, s8, t0; add t1, s7, t1; addi a0, t1, 1
  la a1, enrg_sender_addr; jal ra, address_from_pubkey
  mv a0, s2; mv a1, s3; la a2, enrg_bal_count
  jal ra, rlp_list_count_items
  bnez a0, .Lenrg_next_tx
  la t0, enrg_bal_index; sd zero, 0(t0)
.Lenrg_bal_loop:
  la t0, enrg_bal_index; ld t5, 0(t0)
  la t0, enrg_bal_count; ld t6, 0(t0)
  beq t5, t6, .Lenrg_next_tx
  mv a0, s2; mv a1, s3; mv a2, t5; la a3, enrg_item_off; la a4, enrg_item_len
  jal ra, rlp_item_span
  bnez a0, .Lenrg_next_bal
  la t0, enrg_item_off; ld t0, 0(t0); add t0, s2, t0; la t1, enrg_acct_ptr; sd t0, 0(t1)
  la t1, enrg_item_len; ld t1, 0(t1); la t2, enrg_acct_len; sd t1, 0(t2)
  mv a0, t0; mv a1, t1; li a2, 0; la a3, enrg_addr_off; la a4, enrg_addr_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lenrg_next_bal
  la t0, enrg_addr_len; ld t1, 0(t0); li t2, 20; bne t1, t2, .Lenrg_next_bal
  la t0, enrg_acct_ptr; ld t0, 0(t0); la t1, enrg_addr_off; ld t1, 0(t1); add t0, t0, t1
  la t2, enrg_sender_addr; li t3, 20
.Lenrg_addr_cmp:
  beqz t3, .Lenrg_addr_match
  lbu t4, 0(t0); lbu a7, 0(t2); bne t4, a7, .Lenrg_next_bal
  addi t0, t0, 1; addi t2, t2, 1; addi t3, t3, -1; j .Lenrg_addr_cmp
.Lenrg_addr_match:
  la t0, enrg_acct_ptr; ld a0, 0(t0); la t0, enrg_acct_len; ld a1, 0(t0); li a2, 4; la a3, enrg_nonce_off; la a4, enrg_nonce_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lenrg_next_bal
  la t0, enrg_acct_ptr; ld t0, 0(t0); la t1, enrg_nonce_off; ld t1, 0(t1); add t0, t0, t1; la t2, enrg_nonce_list_ptr; sd t0, 0(t2)
  la t0, enrg_nonce_len; ld a1, 0(t0); la t0, enrg_nonce_list_ptr; ld a0, 0(t0); la a2, enrg_nonce_count
  jal ra, rlp_list_count_items
  bnez a0, .Lenrg_next_bal
  la t0, enrg_nonce_index; sd zero, 0(t0)
.Lenrg_nonce_loop:
  la t0, enrg_nonce_index; ld t3, 0(t0)
  la t0, enrg_nonce_count; ld t4, 0(t0)
  beq t3, t4, .Lenrg_next_bal
  la t0, enrg_nonce_list_ptr; ld a0, 0(t0); la t0, enrg_nonce_len; ld a1, 0(t0); mv a2, t3; la a3, enrg_change_off; la a4, enrg_change_len
  jal ra, rlp_item_span
  bnez a0, .Lenrg_next_nonce
  la t0, enrg_nonce_list_ptr; ld t0, 0(t0); la t1, enrg_change_off; ld t1, 0(t1); add t0, t0, t1; la t2, enrg_change_ptr; sd t0, 0(t2)
  la t1, enrg_change_len; ld t1, 0(t1); la t2, enrg_change_item_len; sd t1, 0(t2)
  mv a0, t0; mv a1, t1; li a2, 0; la a3, enrg_change_index
  jal ra, rlp_field_to_u64
  bnez a0, .Lenrg_next_nonce
  la t0, enrg_change_index; ld t0, 0(t0); addi t1, s8, 1; bgeu t0, t1, .Lenrg_next_nonce
  la t0, enrg_change_ptr; ld a0, 0(t0); la t0, enrg_change_item_len; ld a1, 0(t0); li a2, 1; la a3, enrg_change_value
  jal ra, rlp_field_to_u64
  bnez a0, .Lenrg_next_nonce
  la t0, enrg_change_value; ld t0, 0(t0); la t1, enrg_tx_nonce; ld t1, 0(t1); bgtu t0, t1, .Lenrg_fail
.Lenrg_next_nonce:
  la t0, enrg_nonce_index; ld t3, 0(t0); addi t3, t3, 1; sd t3, 0(t0); j .Lenrg_nonce_loop
.Lenrg_next_bal:
  la t0, enrg_bal_index; ld t5, 0(t0); addi t5, t5, 1; sd t5, 0(t0); j .Lenrg_bal_loop
.Lenrg_next_tx:
  addi s8, s8, 1; j .Lenrg_tx_loop
.Lenrg_ok:
  li a0, 0; j .Lenrg_ret
.Lenrg_fail:
  li a0, 1
.Lenrg_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 128
  ret
