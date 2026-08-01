block_verdict_eip7702_auth_nonstorage_effects_array:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  sd a6, 80(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s8, a5
  li t0, 4; bltu s1, t0, .Lbv7702nse_ok
  mv a0, s0; jal ra, bgv_u32le; andi t0, a0, 3; bnez t0, .Lbv7702nse_ok; bgtu a0, s1, .Lbv7702nse_ok
  srli s5, a0, 2; bne s5, s2, .Lbv7702nse_ok; li s6, 0
.Lbv7702nse_loop:
  beq s6, s5, .Lbv7702nse_ok
  ld a6, 80(sp); slli t0, s6, 3; add t0, a6, t0; ld t0, 0(t0); beq t0, zero, .Lbv7702nse_next
  slli t0, s6, 2; add a0, s0, t0; jal ra, bgv_u32le; mv s7, a0
  slli t0, s5, 2; bltu s7, t0, .Lbv7702nse_next; bgtu s7, s1, .Lbv7702nse_next
  addi t0, s6, 1; beq t0, s5, .Lbv7702nse_last
  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le; j .Lbv7702nse_have
.Lbv7702nse_last:
  mv a0, s1
.Lbv7702nse_have:
  bltu a0, s7, .Lbv7702nse_next; bgtu a0, s1, .Lbv7702nse_next
  add a1, s0, s7; sub a1, a0, s7; add a0, s0, s7; mv a2, s3; mv a3, s4; mv a4, s8
  jal ra, eip7702_auth_nonstorage_effects
.Lbv7702nse_next:
  addi s6, s6, 1; j .Lbv7702nse_loop
.Lbv7702nse_ok:
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 96
  ret
