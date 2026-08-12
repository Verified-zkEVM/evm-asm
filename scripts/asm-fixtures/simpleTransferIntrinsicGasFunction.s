simple_transfer_intrinsic_gas:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0
  li s1, 12000                 # Amsterdam TX_BASE
  li s2, 12000                 # v0.6.0 calldata floor base = TX_BASE + recipient regular gas
  ld a0, 24(s0); la a1, bmvmx_sender_addr; jal ra, address_from_pubkey
  la t0, bmvmx_sender_addr; addi t1, s0, 72; li t2, 20
.Lstig_self_cmp:
  beqz t2, .Lstig_sender_done
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lstig_not_self
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lstig_self_cmp
.Lstig_not_self:
  li t5, 3000; add s1, s1, t5; add s2, s2, t5  # COLD_ACCOUNT_ACCESS (also anchors the floor)
  ld t0, 96(s0); ld t1, 104(s0); or t0, t0, t1
  ld t1, 112(s0); or t0, t0, t1
  ld t1, 120(s0); or t0, t0, t1
  beqz t0, .Lstig_sender_done
  li t5, 6000; add s1, s1, t5; add s2, s2, t5  # TRANSFER_LOG + TX_VALUE (also anchors the floor)
.Lstig_sender_done:
  ld s3, 56(s0)                # calldata ptr
  ld s4, 64(s0)                # calldata len
.Lstig_data_loop:
  beqz s4, .Lstig_access_list
  lbu t0, 0(s3)
  beqz t0, .Lstig_zero_byte
  addi s1, s1, 16
  addi s2, s2, 64
  j .Lstig_data_step
.Lstig_zero_byte:
  addi s1, s1, 4
  addi s2, s2, 64
.Lstig_data_step:
  addi s3, s3, 1
  addi s4, s4, -1
  j .Lstig_data_loop
.Lstig_access_list:
  la t0, runtime_tx_access_list_address_count; sd zero, 0(t0)
  la t0, runtime_tx_access_list_storage_key_count; sd zero, 0(t0)
  ld t0, 160(s0)
  beqz t0, .Lstig_store_done
  li a2, 7; li t1, 1; beq t0, t1, .Lstig_access_field
  li a2, 8; li t1, 2; beq t0, t1, .Lstig_access_field
  li t1, 3; beq t0, t1, .Lstig_access_field
  li t1, 4; beq t0, t1, .Lstig_access_field
  j .Lstig_store_done
.Lstig_access_field:
  ld a0, 176(s0); ld a1, 184(s0); la a3, bsg_access_off; la a4, bsg_access_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lstig_fail
  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1
  la t1, bsg_access_len; ld a1, 0(t1)
  la a2, runtime_tx_access_list_address_count; la a3, runtime_tx_access_list_storage_key_count
  jal ra, access_list_count
  bnez a0, .Lstig_fail
  la t0, runtime_tx_access_list_address_count; ld t1, 0(t0)
.Lstig_addr_loop:
  beqz t1, .Lstig_slot_count
  li t2, 4280
  add s1, s1, t2
  li t2, 1280
  add s2, s2, t2
  addi t1, t1, -1
  j .Lstig_addr_loop
.Lstig_slot_count:
  la t0, runtime_tx_access_list_storage_key_count; ld t1, 0(t0)
.Lstig_slot_loop:
  beqz t1, .Lstig_store_done
  li t2, 5048
  add s1, s1, t2
  li t2, 2048
  add s2, s2, t2
  addi t1, t1, -1
  j .Lstig_slot_loop
.Lstig_store_done:
  ld t0, 160(s0); li t1, 4; bne t0, t1, .Lstig_auth_done
  ld a0, 176(s0); ld a1, 184(s0); li a2, 9; la a3, bsg_access_off; la a4, bsg_access_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lstig_fail
  ld t0, 176(s0); la t1, bsg_access_off; ld t1, 0(t1); add a0, t0, t1
  la t1, bsg_access_len; ld a1, 0(t1); la a2, teer_auth_count
  jal ra, rlp_list_count_items
  bnez a0, .Lstig_fail
  la t0, teer_auth_count; ld t1, 0(t0); li t2, 7816; mul t1, t1, t2; add s1, s1, t1
.Lstig_auth_done:
  la t0, runtime_tx_calldata_floor; sd s2, 0(t0)
  la t0, runtime_tx_intrinsic_regular; sd s1, 0(t0)
  sd s1, 48(sp); sd s2, 56(sp)
  la t0, bvgr_tx_state_gas; ld t1, 0(t0)
  ld s1, 48(sp); ld s2, 56(sp)
  la t2, runtime_tx_auth_regular_refund; ld t2, 0(t2); add s1, s1, t2
  la t0, runtime_tx_intrinsic_regular; sd s1, 0(t0)
  li a0, 0; mv a1, s1; mv a2, s2; mv a3, t1
  j .Lstig_ret
.Lstig_fail:
  li a0, 1; li a1, 0; li a2, 0; li a3, 0
.Lstig_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 64
  ret
