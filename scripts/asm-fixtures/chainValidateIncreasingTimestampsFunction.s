chain_validate_increasing_timestamps:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  li t0, 1
  sd t0, 0(s3); sd zero, 0(s4)
  li t0, 2
  bltu s0, t0, .Lcvit_done
  # Extract headers[0].timestamp into s5 (prev_ts)
  ld a1, 0(s1)
  mv a0, s2
  li a2, 11
  la a3, cvit_ts
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lcvit_propagate
  la t0, cvit_ts; ld s5, 0(t0)
  # Walk: parent_ptr = headers[0]; for i in [0, N-1): parent=headers[i], child=headers[i+1]
  ld t0, 0(s1)
  add t1, s2, t0              # child_ptr starts at headers[1]
  li t2, 1                    # i = 1
.Lcvit_loop:
  beq t2, s0, .Lcvit_done
  la t0, cvit_iter_child; sd t1, 0(t0)
  la t0, cvit_iter_i;     sd t2, 0(t0)
  la t0, cvit_iter_prev;  sd s5, 0(t0)
  slli t3, t2, 3
  add t3, s1, t3
  ld a1, 0(t3)                # header_len
  mv a0, t1
  li a2, 11
  la a3, cvit_ts
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lcvit_propagate
  la t0, cvit_ts;          ld t3, 0(t0)
  la t0, cvit_iter_prev;   ld t4, 0(t0)
  bgeu t4, t3, .Lcvit_pred_false
  # advance
  la t0, cvit_iter_child;  ld t1, 0(t0)
  la t0, cvit_iter_i;      ld t2, 0(t0)
  mv s5, t3                   # prev_ts = current
  slli t5, t2, 3
  add t5, s1, t5
  ld t6, 0(t5)
  add t1, t1, t6
  addi t2, t2, 1
  j .Lcvit_loop
.Lcvit_pred_false:
  sd zero, 0(s3)
  la t0, cvit_iter_i; ld t1, 0(t0)
  sd t1, 0(s4)
  li a0, 0
  j .Lcvit_ret
.Lcvit_propagate:
  la t0, cvit_iter_i; ld t1, 0(t0)
  sd t1, 0(s4)
  j .Lcvit_ret
.Lcvit_done:
  li a0, 0
.Lcvit_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
