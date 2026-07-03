bal_section_info:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # SSZ_BASE
  mv s3, a1                   # out ptr cell
  mv s4, a2                   # out len cell
  mv s5, a3                   # out count cell
  addi s1, s0, 16             # NPR = SSZ_BASE+16
  addi s2, s0, 60             # exec_payload = SSZ_BASE+60
  addi a0, s2, 528; jal ra, bgv_u32le
  add t0, s2, a0              # bal_start
  sd t0, 0(s3)
  addi a0, s1, 4; jal ra, bgv_u32le
  add t1, s1, a0              # bal_end
  ld t0, 0(s3); sub t1, t1, t0
  sd t1, 0(s4)
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_init
  bnez a2, .Lbsi_fail
  mv s1, a0; mv s2, a1; li s0, 0
.Lbsi_count_loop:
  mv a0, s1; mv a1, s2; jal ra, rlp_walk_next
  li t0, 2; beq a1, t0, .Lbsi_count_done
  bnez a1, .Lbsi_fail
  mv s1, a0; addi s0, s0, 1; j .Lbsi_count_loop
.Lbsi_count_done:
  sd s0, 0(s5)
  li a0, 0; j .Lbsi_ret
.Lbsi_fail:
  li a0, 1
.Lbsi_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
