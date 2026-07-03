chain_validate_extra_data_length:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  li t0, 1
  sd t0, 0(s3); sd zero, 0(s4)
  li s5, 0
.Lcvedl_loop:
  beq s5, s0, .Lcvedl_done
  la t0, cvedl_iter_ptr; sd s2, 0(t0)
  la t0, cvedl_iter_i;   sd s5, 0(t0)
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 12
  la a3, cvedl_offset; la a4, cvedl_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lcvedl_propagate
  la t0, cvedl_iter_ptr; ld s2, 0(t0)
  la t0, cvedl_iter_i;   ld s5, 0(t0)
  la t0, cvedl_length; ld t1, 0(t0)
  li t2, 32
  bgtu t1, t2, .Lcvedl_violation
  slli t3, s5, 3
  add t3, s1, t3
  ld t4, 0(t3)
  add s2, s2, t4
  addi s5, s5, 1
  j .Lcvedl_loop
.Lcvedl_violation:
  sd zero, 0(s3)
  sd s5, 0(s4)
  li a0, 0
  j .Lcvedl_ret
.Lcvedl_propagate:
  sd s5, 0(s4)
  li a0, 1
  j .Lcvedl_ret
.Lcvedl_done:
  li a0, 0
.Lcvedl_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
