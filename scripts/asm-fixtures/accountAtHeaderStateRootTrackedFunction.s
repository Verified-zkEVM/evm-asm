account_at_header_state_root_tracked:
  addi sp, sp, -64
  sd ra, 0(sp); sd a0, 8(sp); sd a1, 16(sp); sd a2, 24(sp)
  sd a3, 32(sp); sd a4, 40(sp); sd a5, 48(sp); sd a6, 56(sp)
  mv a0, a2
  jal ra, account_read_record
  ld ra, 0(sp); ld a0, 8(sp); ld a1, 16(sp); ld a2, 24(sp)
  ld a3, 32(sp); ld a4, 40(sp); ld a5, 48(sp); ld a6, 56(sp)
  addi sp, sp, 64
  j account_at_header_state_root
