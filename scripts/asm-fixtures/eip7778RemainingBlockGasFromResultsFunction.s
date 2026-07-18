eip7778_remaining_block_gas_from_results:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  sd s6, 56(sp)
  sd s7, 64(sp)
  sd s8, 72(sp)
  mv s8, a7
  mv s0, a0
  mv s1, a1
  mv s2, a2
  mv s3, a3
  mv s4, a4
  mv s5, a5
  mv s6, a6
  li s7, 0
.Le7778fr_loop:
  beq s7, s5, .Le7778fr_check
  slli t0, s7, 3
  add t1, s1, t0
  ld a0, 0(t1)
  add t1, s2, t0
  ld a1, 0(t1)
  add t1, s3, t0
  ld a2, 0(t1)
  add t1, s4, t0
  ld a3, 0(t1)
  jal ra, tx_gas_result_increments
  bnez a0, .Le7778fr_badresult
  beqz s8, .Le7778fr_store
  slli t0, s7, 3
  add t1, s8, t0
  ld t2, 0(t1)
  bltu a3, t2, .Le7778fr_stateover
  sub a3, a3, t2
  add t1, s4, t0
  ld t2, 0(t1)
  bgeu a3, t2, .Le7778fr_floored
  mv a3, t2
.Le7778fr_floored:
  mv a1, a3
.Le7778fr_store:
  slli t0, s7, 3
  add t1, s6, t0
  sd a1, 0(t1)
  addi s7, s7, 1
  j .Le7778fr_loop
.Le7778fr_check:
  mv a0, s0
  mv a1, s1
  mv a2, s6
  mv a3, s5
  mv a4, s8
  jal ra, eip7778_remaining_block_gas_check
  j .Le7778fr_ret
.Le7778fr_badresult:
  li a0, 3
  addi a1, s7, 1
  li a2, 0
  j .Le7778fr_ret
.Le7778fr_stateover:
  li a0, 4
  addi a1, s7, 1
  li a2, 0
.Le7778fr_ret:
  ld ra, 0(sp)
  ld s0, 8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  ld s5, 48(sp)
  ld s6, 56(sp)
  ld s7, 64(sp)
  ld s8, 72(sp)
  addi sp, sp, 80
  ret
