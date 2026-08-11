multi_tx_nth_context:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # output record ptr
  mv s4, a1                   # transaction index i
  mv t0, s0; li t1, 24
.Lmtx_zero:
  beqz t1, .Lmtx_zero_done
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; j .Lmtx_zero
.Lmtx_zero_done:
  la t0, bv_tx_list_ptr; ld s1, 0(t0)   # SSZ tx list ptr
  la t0, bv_tx_list_len; ld s2, 0(t0)   # tx list len
  li t0, 4; bltu s2, t0, .Lmtx_malformed
  mv a0, s1; jal ra, bgv_u32le           # offset[0]
  andi t0, a0, 3; bnez t0, .Lmtx_malformed
  srli s3, a0, 2                         # tx count = offset[0] / 4
  bgeu s4, s3, .Lmtx_oob
  slli t0, s4, 2; add a0, s1, t0; jal ra, bgv_u32le
  mv s5, a0                              # offset[i]
  addi t0, s4, 1; beq t0, s3, .Lmtx_last
  slli t1, t0, 2; add a0, s1, t1; jal ra, bgv_u32le
  mv s6, a0                              # offset[i+1]
  j .Lmtx_have_next
.Lmtx_last:
  mv s6, s2                              # final tx ends at list end
.Lmtx_have_next:
  slli t0, s3, 2; bltu s5, t0, .Lmtx_malformed   # offset[i] must be past table
  bltu s6, s5, .Lmtx_malformed
  bgtu s6, s2, .Lmtx_malformed
  add s1, s1, s5                         # tx ptr
  sub s2, s6, s5                         # tx len
  beqz s2, .Lmtx_item_empty
  sd s1, 8(s0); sd s2, 16(s0)
  mv a0, s1; mv a1, s2; la a2, tea_type; la a3, tea_inner_off
  jal ra, tx_type_dispatch
  beqz a0, .Lmtx_type_ok
  li t0, 20; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_type_ok:
  la t0, tea_type; ld t1, 0(t0); sd t1, 160(s0)
  la t0, tea_inner_off; ld t3, 0(t0); sd t3, 168(s0)
  bltu s2, t3, .Lmtx_inner_oob
  add t4, s1, t3; sd t4, 176(s0)
  sub t4, s2, t3; sd t4, 184(s0)
  mv a0, s1; mv a1, s2; la a2, sttc_nonce; addi a3, s0, 40
  jal ra, tx_extract_nonce_and_gas
  sd a0, 128(s0)
  beqz a0, .Lmtx_gas_ok
  li t0, 20; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_gas_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 72; addi a3, s0, 48
  jal ra, tx_extract_to_address
  sd a0, 136(s0)
  beqz a0, .Lmtx_to_ok
  li t0, 30; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_to_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 96
  jal ra, tx_extract_value
  sd a0, 144(s0)
  beqz a0, .Lmtx_value_ok
  li t0, 40; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_value_ok:
  mv a0, s1; mv a1, s2; addi a2, s0, 56; addi a3, s0, 64
  jal ra, tx_extract_data_section
  sd a0, 152(s0)
  beqz a0, .Lmtx_data_ok
  li t0, 50; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_data_ok:
.Lmtx_not_creation:
.Lmtx_ok:
  sd zero, 0(s0); j .Lmtx_ret
.Lmtx_malformed:
  li t0, 3; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_oob:
  li t0, 5; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_item_empty:
  li t0, 4; sd t0, 0(s0); j .Lmtx_ret
.Lmtx_inner_oob:
  li t0, 21; sd t0, 0(s0)
.Lmtx_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
