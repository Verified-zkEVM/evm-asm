simple_transfer_tx_context:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # output ptr
  sd zero,   0(s0); sd zero,   8(s0); sd zero,  16(s0); sd zero,  24(s0)
  sd zero,  32(s0); sd zero,  40(s0); sd zero,  48(s0); sd zero,  56(s0)
  sd zero,  64(s0); sd zero,  72(s0); sd zero,  80(s0); sd zero,  88(s0)
  sd zero,  96(s0); sd zero, 104(s0); sd zero, 112(s0); sd zero, 120(s0)
  sd zero, 128(s0); sd zero, 136(s0); sd zero, 144(s0); sd zero, 152(s0)
  sd zero, 160(s0); sd zero, 168(s0); sd zero, 176(s0); sd zero, 184(s0)
  la t0, bv_tx_count; ld t1, 0(t0); li t2, 1; beq t1, t2, .Lsttc_count_ok
  li t0, 1; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_count_ok:
  la t0, bv_public_keys_len; ld t1, 0(t0); li t2, 65; beq t1, t2, .Lsttc_pubkey_ok
  li t0, 2; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_pubkey_ok:
  la t0, bv_tx_list_ptr; ld s1, 0(t0)
  la t0, bv_tx_list_len; ld s2, 0(t0)
  la t0, bv_tx_item_start; ld s3, 0(t0)
  bltu s2, s3, .Lsttc_item_oob
  beq s2, s3, .Lsttc_item_empty
  add s1, s1, s3              # tx ptr
  sub s2, s2, s3              # tx len
  sd s1, 8(s0); sd s2, 16(s0)
  la t0, bv_public_keys_ptr; ld t1, 0(t0); addi t1, t1, 1; sd t1, 24(s0)
  la t0, bv_exec_p; ld t1, 0(t0); addi t1, t1, 440
  la t2, sttc_base_fee_be; li t3, 0
.Lsttc_base_fee_rev:
  li t4, 32; beq t3, t4, .Lsttc_base_fee_done
  sub t5, t4, t3; addi t5, t5, -1; add t5, t1, t5
  lbu t6, 0(t5); add t5, t2, t3; sb t6, 0(t5)
  addi t3, t3, 1; j .Lsttc_base_fee_rev
.Lsttc_base_fee_done:
  sd t2, 32(s0)
  mv a0, s1; mv a1, s2; la a2, tea_type; la a3, tea_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Lsttc_type_ok
  li t0, 20; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_type_ok:
  la t0, tea_type; ld t1, 0(t0); sd t1, 160(s0)
  la t0, tea_inner_off; ld t3, 0(t0); sd t3, 168(s0)
  bltu s2, t3, .Lsttc_inner_oob
  add t4, s1, t3; sd t4, 176(s0)
  sub t4, s2, t3; sd t4, 184(s0)
  mv a0, s1; mv a1, s2; la a2, sttc_nonce; addi a3, s0, 40
  jal ra, tx_extract_nonce_and_gas
  sd a0, 128(s0)
  beqz a0, .Lsttc_gas_ok
  li t0, 20; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_gas_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 72; addi a3, s0, 48
  jal ra, tx_extract_to_address
  sd a0, 136(s0)
  beqz a0, .Lsttc_to_ok
  li t0, 30; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_to_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 96
  jal ra, tx_extract_value
  sd a0, 144(s0)
  beqz a0, .Lsttc_value_ok
  li t0, 40; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_value_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 56; addi a3, s0, 64
  jal ra, tx_extract_data_section
  sd a0, 152(s0)
  beqz a0, .Lsttc_data_ok
  li t0, 50; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_data_ok:
.Lsttc_not_creation:
.Lsttc_ok:
  sd zero, 0(s0); j .Lsttc_ret
.Lsttc_item_oob:
  li t0, 3; sd t0, 0(s0); j .Lsttc_ret
.Lsttc_item_empty:
  li t0, 4; sd t0, 0(s0)
  j .Lsttc_ret
.Lsttc_inner_oob:
  li t0, 21; sd t0, 0(s0)
.Lsttc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
