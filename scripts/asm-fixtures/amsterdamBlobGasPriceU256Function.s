amsterdam_blob_gas_price_u256:
  addi sp, sp, -208
  sd ra, 0(sp)
  sd s0, 8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  sd s6, 56(sp)
  mv s0, a0
  mv s5, a1
  lui s1, 2853
  addiw s1, s1, -1217
  li s2, 1
  addi s3, sp, 64
  addi s4, sp, 112
  addi s6, sp, 160
  sd zero, 64(sp)
  sd zero, 72(sp)
  sd zero, 80(sp)
  sd zero, 88(sp)
  sd zero, 96(sp)
  sd zero, 104(sp)
  sd zero, 112(sp)
  sd zero, 120(sp)
  sd zero, 128(sp)
  sd zero, 136(sp)
  sd zero, 144(sp)
  sd zero, 152(sp)
  sd zero, 160(sp)
  sd zero, 168(sp)
  sd zero, 176(sp)
  sd zero, 184(sp)
  sd zero, 192(sp)
  sd zero, 200(sp)
  sd s1, 64(sp)
.Ltaylor_loop:
  li t0, 0
  ld t1, 0(s3)
  or t0, t0, t1
  ld t1, 8(s3)
  or t0, t0, t1
  ld t1, 16(s3)
  or t0, t0, t1
  ld t1, 24(s3)
  or t0, t0, t1
  ld t1, 32(s3)
  or t0, t0, t1
  ld t1, 40(s3)
  or t0, t0, t1
  beqz t0, .Ltaylor_final_div
  li t0, 496
  bgeu s2, t0, .Ltaylor_fail
  li t0, 0
  ld t1, 0(s3)
  ld t2, 0(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 0(s6)
  mv t0, t4
  ld t1, 8(s3)
  ld t2, 8(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 8(s6)
  mv t0, t4
  ld t1, 16(s3)
  ld t2, 16(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 16(s6)
  mv t0, t4
  ld t1, 24(s3)
  ld t2, 24(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 24(s6)
  mv t0, t4
  ld t1, 32(s3)
  ld t2, 32(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 32(s6)
  mv t0, t4
  ld t1, 40(s3)
  ld t2, 40(s6)
  add t3, t1, t2
  sltu t4, t3, t1
  add t5, t3, t0
  sltu t6, t5, t3
  or t4, t4, t6
  sd t5, 40(s6)
  mv t0, t4
  bnez t0, .Ltaylor_fail
  li t6, 0
  ld t0, 0(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 0(s4)
  mv t6, t5
  ld t0, 8(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 8(s4)
  mv t6, t5
  ld t0, 16(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 16(s4)
  mv t6, t5
  ld t0, 24(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 24(s4)
  mv t6, t5
  ld t0, 32(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 32(s4)
  mv t6, t5
  ld t0, 40(s3)
  mul t1, t0, s0
  mulhu t2, t0, s0
  add t3, t1, t6
  sltu t4, t3, t1
  add t5, t2, t4
  sltu t4, t5, t2
  bnez t4, .Ltaylor_fail
  sd t3, 40(s4)
  mv t6, t5
  bnez t6, .Ltaylor_fail
  mv t0, s3
  mv s3, s4
  mv s4, t0
  mul t0, s1, s2
  mulhu t1, s1, s2
  bnez t1, .Ltaylor_fail
  mv t1, zero
  mv t5, s3
  addi t5, t5, 40
  li t6, 6
.Ltaylor_div_limb:
  ld t2, 0(t5)
  li t3, 0
  li t4, 64
.Ltaylor_div_bit:
  slli t1, t1, 1
  bltz t2, .Ltaylor_div_one
  slli t2, t2, 1
  j .Ltaylor_div_after_bit
.Ltaylor_div_one:
  slli t2, t2, 1
  addi t1, t1, 1
.Ltaylor_div_after_bit:
  slli t3, t3, 1
  bltu t1, t0, .Ltaylor_div_no_sub
  sub t1, t1, t0
  addi t3, t3, 1
.Ltaylor_div_no_sub:
  addi t4, t4, -1
  bnez t4, .Ltaylor_div_bit
  sd t3, 0(t5)
  addi t5, t5, -8
  addi t6, t6, -1
  bnez t6, .Ltaylor_div_limb
  addi s2, s2, 1
  j .Ltaylor_loop
.Ltaylor_final_div:
  mv t0, s1
  mv t1, zero
  mv t5, s6
  addi t5, t5, 40
  li t6, 6
.Ltaylor_final_div_limb:
  ld t2, 0(t5)
  li t3, 0
  li t4, 64
.Ltaylor_final_div_bit:
  slli t1, t1, 1
  bltz t2, .Ltaylor_final_div_one
  slli t2, t2, 1
  j .Ltaylor_final_div_after_bit
.Ltaylor_final_div_one:
  slli t2, t2, 1
  addi t1, t1, 1
.Ltaylor_final_div_after_bit:
  slli t3, t3, 1
  bltu t1, t0, .Ltaylor_final_div_no_sub
  sub t1, t1, t0
  addi t3, t3, 1
.Ltaylor_final_div_no_sub:
  addi t4, t4, -1
  bnez t4, .Ltaylor_final_div_bit
  sd t3, 0(t5)
  addi t5, t5, -8
  addi t6, t6, -1
  bnez t6, .Ltaylor_final_div_limb
  ld t0, 32(s6)
  ld t1, 40(s6)
  or t0, t0, t1
  bnez t0, .Ltaylor_fail
  li t5, 0
.Ltaylor_copy:
  li t4, 31
  sub t4, t4, t5
  add t3, s6, t4
  lbu t2, 0(t3)
  add t3, s5, t5
  sb t2, 0(t3)
  addi t5, t5, 1
  li t4, 32
  bltu t5, t4, .Ltaylor_copy
  li a0, 0
  j .Ltaylor_return
.Ltaylor_fail:
  li a0, 1
.Ltaylor_return:
  ld ra, 0(sp)
  ld s0, 8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  ld s5, 48(sp)
  ld s6, 56(sp)
  addi sp, sp, 208
  ret
