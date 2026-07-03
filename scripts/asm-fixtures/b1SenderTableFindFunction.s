b1_sender_table_find:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2
  li s3, 0; mv s4, s1
.Lb1stf_loop:
  bgeu s3, s4, .Lb1stf_absent
  add s5, s3, s4; srli s5, s5, 1
  li t0, 40; mul t0, s5, t0; add t1, s0, t0
  li t2, 0
.Lb1stf_cmp:
  li t3, 20; beq t2, t3, .Lb1stf_found
  add t3, t1, t2; lbu t4, 0(t3); add t3, s2, t2; lbu t5, 0(t3)
  bltu t4, t5, .Lb1stf_entry_less
  bltu t5, t4, .Lb1stf_entry_greater
  addi t2, t2, 1; j .Lb1stf_cmp
.Lb1stf_entry_less:
  addi s3, s5, 1; j .Lb1stf_loop
.Lb1stf_entry_greater:
  mv s4, s5; j .Lb1stf_loop
.Lb1stf_found:
  li a0, 0; mv a1, t1; j .Lb1stf_ret
.Lb1stf_absent:
  li a0, 1
.Lb1stf_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
