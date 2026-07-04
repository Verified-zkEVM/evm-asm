tx_gas_sender_bal_lookup:
  addi sp, sp, -112
  sd ra,   0(sp)
  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)
  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)
  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # pubkey ptr
  mv s3, a3                   # BAL ptr
  mv s4, a4                   # BAL len
  mv s5, a5                   # pre-account records ptr
  mv s6, a6                   # output ptr
  # Clear fixed output area and install absent sentinels.
  sd zero,   0(s6); sd zero,  16(s6); sd zero,  24(s6); sd zero,  32(s6)
  sd zero,  40(s6); sd zero,  48(s6); sd zero,  56(s6); sd zero,  64(s6)
  sd zero,  72(s6); sd zero,  80(s6); sd zero,  96(s6); sd zero, 104(s6)
  sd zero, 112(s6); sd zero, 136(s6); sd zero, 144(s6); sd zero, 152(s6)
  sd zero, 160(s6)
  li t0, -1; sd t0, 8(s6); sd t0, 88(s6); sd t0, 128(s6)
  # Validate tx envelope shape. Sender recovery itself is provided by the
  # selected EEST public key, matching existing BAL sender-scan helpers.
  beqz s1, .Ltgsbl_bad_tx
  lbu t0, 0(s0)
  li t1, 0x80
  bltu t0, t1, .Ltgsbl_typed_tx
  mv a0, s0; mv a1, s1; li a2, 0; la a3, tgsbl_tmp_off; la a4, tgsbl_tmp_len
  jal ra, rlp_list_nth_item
  bnez a0, .Ltgsbl_bad_tx
  j .Ltgsbl_have_tx
.Ltgsbl_typed_tx:
  beqz t0, .Ltgsbl_bad_tx
  li t1, 4; bgtu t0, t1, .Ltgsbl_bad_tx
  li t1, 2; bltu s1, t1, .Ltgsbl_bad_tx
  addi a0, s0, 1; addi a1, s1, -1; li a2, 0; la a3, tgsbl_tmp_off; la a4, tgsbl_tmp_len
  jal ra, rlp_list_nth_item
  bnez a0, .Ltgsbl_bad_tx
.Ltgsbl_have_tx:
  mv a0, s2; addi a1, s6, 16
  jal ra, address_from_pubkey
  mv a0, s3; mv a1, s4; la a2, tgsbl_count
  jal ra, rlp_list_count_items
  bnez a0, .Ltgsbl_bad_bal
  la t0, tgsbl_count; ld s8, 0(t0)
  li s9, 0                    # row index
.Ltgsbl_loop:
  bgeu s9, s8, .Ltgsbl_missing
  mv a0, s3; mv a1, s4; mv a2, s9; la a3, tgsbl_row_off; la a4, tgsbl_row_len
  jal ra, rlp_item_span
  bnez a0, .Ltgsbl_bad_bal
  la t0, tgsbl_row_off; ld t0, 0(t0); add s10, s3, t0
  la t0, tgsbl_row_len; ld s11, 0(t0)
  mv a0, s10; mv a1, s11; li a2, 0; la a3, tgsbl_addr_off; la a4, tgsbl_addr_len
  jal ra, rlp_list_nth_item
  bnez a0, .Ltgsbl_bad_bal
  la t0, tgsbl_addr_len; ld t0, 0(t0); li t1, 20; bne t0, t1, .Ltgsbl_bad_bal
  la t0, tgsbl_addr_off; ld t0, 0(t0); add t0, s10, t0
  addi t1, s6, 16
  li t2, 20
.Ltgsbl_cmp:
  beqz t2, .Ltgsbl_match
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Ltgsbl_next
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1
  j .Ltgsbl_cmp
.Ltgsbl_next:
  addi s9, s9, 1
  j .Ltgsbl_loop
.Ltgsbl_match:
  sd s9, 8(s6)
  slli t0, s9, 4; slli t1, s9, 3; add t0, t0, t1; add t0, s5, t0
  ld a0, 0(t0); ld a1, 8(t0); addi a2, s6, 48
  jal ra, account_extract_balance
  bnez a0, .Ltgsbl_bad_account
  slli t0, s9, 4; slli t1, s9, 3; add t0, t0, t1; add t0, s5, t0
  ld a0, 0(t0); ld a1, 8(t0); addi a2, s6, 80
  jal ra, account_extract_nonce
  bnez a0, .Ltgsbl_bad_account
  mv a0, s10; mv a1, s11; addi a2, s6, 96; addi a3, s6, 88; addi a4, s6, 136; addi a5, s6, 128
  jal ra, bal_account_post_fields
  bnez a0, .Ltgsbl_bad_post
  li a0, 0
  j .Ltgsbl_store_status
.Ltgsbl_bad_tx:
  li a0, 1; j .Ltgsbl_store_status
.Ltgsbl_bad_bal:
  li a0, 2; j .Ltgsbl_store_status
.Ltgsbl_missing:
  li a0, 3; j .Ltgsbl_store_status
.Ltgsbl_bad_account:
  li a0, 4; j .Ltgsbl_store_status
.Ltgsbl_bad_post:
  li a0, 5
.Ltgsbl_store_status:
  sd a0, 0(s6)
  ld ra,   0(sp)
  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)
  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)
  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
