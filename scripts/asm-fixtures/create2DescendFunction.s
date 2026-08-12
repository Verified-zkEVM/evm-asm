create2_descend:
  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, x12                   # stack top (value@0, offset@32, length@64, salt@96)
  mv s1, x13                   # mem base
  mv s2, x20                   # env base
  ld t0, 32(s0); la t1, create_init_offset; sd t0, 0(t1)
  ld t0, 64(s0); la t1, create_init_size;   sd t0, 0(t1)
  la t1, create_sender_be
  ld t2, 0(s2); sd t2, 0(t1); ld t2, 8(s2); sd t2, 8(t1)
  ld t2, 16(s2); sd t2, 16(t1); ld t2, 24(s2); sd t2, 24(t1)
  addi t2, s0, 127; la t1, create_salt_be; li t0, 32
.Lc2d_revsalt:
  beqz t0, .Lc2d_revsalt_d
  lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lc2d_revsalt
.Lc2d_revsalt_d:
  la a0, create_sender_be; la a1, create_salt_be
  la t0, create_init_offset; ld t0, 0(t0); add a2, s1, t0
  la t0, create_init_size; ld a3, 0(t0)
  la a4, create_address_be
  jal ra, address_compute_create2
  mv a0, s1; mv a1, s0; li a2, 1
  jal ra, create_stage_initcode_frame
  jal ra, create_execute_initcode_frame
  addi t4, s0, 96
  sd x0, 0(t4); sd x0, 8(t4); sd x0, 16(t4); sd x0, 24(t4)
  la t0, create_child_status; ld t0, 0(t0); li t1, 2; bne t0, t1, .Lc2d_done
  la t2, create_address_be; addi t2, t2, 19; mv t1, t4; li t0, 20
.Lc2d_revaddr:
  beqz t0, .Lc2d_done
  lbu t3, 0(t2); sb t3, 0(t1); addi t2, t2, -1; addi t1, t1, 1; addi t0, t0, -1; j .Lc2d_revaddr
.Lc2d_done:
  addi a0, s0, 96              # new stack top
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); addi sp, sp, 48
  ret
