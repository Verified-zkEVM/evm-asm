chain_validate_gas_used_under_limit:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  li t0, 1
  sd t0, 0(s3); sd zero, 0(s4)
  li s5, 0
.Lcvgul_loop:
  beq s5, s0, .Lcvgul_done
  la t0, cvgul_iter_ptr; sd s2, 0(t0)
  la t0, cvgul_iter_i;   sd s5, 0(t0)
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 10
  la a3, cvgul_gas_used
  jal ra, rlp_field_to_u64
  bnez a0, .Lcvgul_propagate
  la t0, cvgul_iter_ptr; ld s2, 0(t0)
  la t0, cvgul_iter_i;   ld s5, 0(t0)
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 9
  la a3, cvgul_gas_limit
  jal ra, rlp_field_to_u64
  bnez a0, .Lcvgul_propagate
  la t0, cvgul_iter_ptr; ld s2, 0(t0)
  la t0, cvgul_iter_i;   ld s5, 0(t0)
  la t0, cvgul_gas_used;  ld t1, 0(t0)
  la t0, cvgul_gas_limit; ld t2, 0(t0)
  bgtu t1, t2, .Lcvgul_violation
  slli t3, s5, 3
  add t3, s1, t3
  ld t4, 0(t3)
  add s2, s2, t4
  addi s5, s5, 1
  j .Lcvgul_loop
.Lcvgul_violation:
  sd zero, 0(s3)
  sd s5, 0(s4)
  li a0, 0
  j .Lcvgul_ret
.Lcvgul_propagate:
  sd s5, 0(s4)
  j .Lcvgul_ret
.Lcvgul_done:
  li a0, 0
.Lcvgul_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
