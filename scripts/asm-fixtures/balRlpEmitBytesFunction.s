bal_rlp_emit_bytes:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3
  li t0, 1; bne s2, t0, .Lbreb_short
  lbu t1, 0(s1); li t2, 0x80; bgeu t1, t2, .Lbreb_short
  mv a0, s0; mv a1, s1; li a2, 1; jal ra, keccak_absorb
  li a0, 1; j .Lbreb_ret
.Lbreb_short:
  li t0, 56; bgeu s2, t0, .Lbreb_long
  li t1, 0x80; add t1, t1, s2; sb t1, 0(s3)
  mv a0, s0; mv a1, s3; li a2, 1; jal ra, keccak_absorb
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, keccak_absorb
  addi a0, s2, 1; j .Lbreb_ret
.Lbreb_long:
  li t0, 0; mv t1, s2
.Lbreb_bc:
  beqz t1, .Lbreb_bc_done; addi t0, t0, 1; srli t1, t1, 8; j .Lbreb_bc
.Lbreb_bc_done:
  li t2, 0xb7; add t2, t2, t0; sb t2, 0(s3)
  mv t3, t0
.Lbreb_len:
  beqz t3, .Lbreb_len_done
  addi t4, t3, -1; slli t4, t4, 3; srl t5, s2, t4; andi t5, t5, 255
  sub t6, t0, t3; addi t6, t6, 1; add t6, s3, t6; sb t5, 0(t6)
  addi t3, t3, -1; j .Lbreb_len
.Lbreb_len_done:
  addi a2, t0, 1
  mv a0, s0; mv a1, s3; jal ra, keccak_absorb
  mv a0, s0; mv a1, s1; mv a2, s2; jal ra, keccak_absorb
  li t0, 0; mv t1, s2
.Lbreb_bc2:
  beqz t1, .Lbreb_bc2_done; addi t0, t0, 1; srli t1, t1, 8; j .Lbreb_bc2
.Lbreb_bc2_done:
  add a0, s2, t0; addi a0, a0, 1
.Lbreb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
