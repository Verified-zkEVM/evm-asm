mpt_indexed_stream_leaf_hash:
  addi sp, sp, -176
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)
  mv s1, a0; mv s2, a1; mv s3, a2; mv s4, a3; mv s5, a4; li t0, 6; bgtu s2, t0, .Lmislh_fail; li t0, 32; bltu s4, t0, .Lmislh_fail
  mv a0, s1; mv a1, s2; li a2, 1; addi a3, sp, 88; jal ra, hp_encode_nibbles; mv s7, a0
  addi a0, sp, 88; mv a1, s7; addi a2, sp, 96; addi a3, sp, 144; jal ra, rlp_encode_bytes; ld s7, 144(sp)
  li t0, 1; bne s4, t0, .Lmislh_value_prefix; lbu t1, 0(s3); li t2, 128; bgeu t1, t2, .Lmislh_value_prefix; li s8, 0; j .Lmislh_value_ready
.Lmislh_value_prefix:
  li a0, 0x80; mv a1, s4; addi a2, sp, 112; jal ra, rlp_prefix_to_buffer; mv s8, a0
.Lmislh_value_ready:
  add t0, s7, s8; add a1, t0, s4; li a0, 0xc0; addi a2, sp, 128; jal ra, rlp_prefix_to_buffer; mv s9, a0
  la s0, zk3_state; mv t0, s0; li t1, 25
.Lmislh_zero:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lmislh_zero
  li s6, 0; addi a0, sp, 128; mv a1, s9; jal ra, .Lmislh_absorb; addi a0, sp, 96; mv a1, s7; jal ra, .Lmislh_absorb; beqz s8, .Lmislh_value
  addi a0, sp, 112; mv a1, s8; jal ra, .Lmislh_absorb
.Lmislh_value:
  mv a0, s3; mv a1, s4; jal ra, .Lmislh_absorb; add t0, s0, s6; lbu t1, 0(t0); xori t1, t1, 0x01; sb t1, 0(t0); addi t0, s0, 135; lbu t1, 0(t0); xori t1, t1, 0x80; sb t1, 0(t0); mv a0, s0; .4byte 0x80052073
  ld t0, 0(s0); sd t0, 0(s5); ld t0, 8(s0); sd t0, 8(s5); ld t0, 16(s0); sd t0, 16(s5); ld t0, 24(s0); sd t0, 24(s5); li a0, 0; j .Lmislh_ret
.Lmislh_fail:
  li a0, 1
.Lmislh_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); addi sp, sp, 176; ret
.Lmislh_absorb:
  beqz a1, .Lmislh_absorb_ret; lbu t0, 0(a0); add t1, s0, s6; lbu t2, 0(t1); xor t2, t2, t0; sb t2, 0(t1); addi a0, a0, 1; addi a1, a1, -1; addi s6, s6, 1; li t3, 136; bne s6, t3, .Lmislh_absorb; sd a0, 160(sp); sd a1, 168(sp); mv a0, s0; .4byte 0x80052073; ld a0, 160(sp); ld a1, 168(sp); li s6, 0; j .Lmislh_absorb
.Lmislh_absorb_ret:
  ret
