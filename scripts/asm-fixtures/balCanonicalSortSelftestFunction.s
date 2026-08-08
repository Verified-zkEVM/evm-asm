bal_canonical_sort_selftest:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0
  li s1, 1
  mv t0, s0; li t1, 64
.Lbalsort_st_zero:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lbalsort_st_zero
  li t1, 0x30; sb t1, 19(s0);   li t1, 1; sb t1, 64(s0)
  addi t0, s0, 128
  li t1, 0x10; sb t1, 19(t0);   li t1, 2; sb t1, 64(t0)
  addi t0, s0, 256
  li t1, 0x40; sb t1, 19(t0);   li t1, 3; sb t1, 64(t0)
  addi t0, s0, 384
  li t1, 0x20; sb t1, 19(t0);   li t1, 4; sb t1, 64(t0)
  mv a0, s0; li a1, 4; li a2, 128; li a3, 0x1400; li a4, 1; li a5, 4
  jal ra, bal_canonical_sort
  bnez a0, .Lbalsort_st_fail
  lbu t1, 64(s0);   li t2, 2; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 128; lbu t1, 64(t0); li t2, 4; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 256; lbu t1, 64(t0); li t2, 1; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 384; lbu t1, 64(t0); li t2, 3; bne t1, t2, .Lbalsort_st_fail
  li s1, 2
  mv t0, s0; li t1, 64
.Lbalsort_st_zero2:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lbalsort_st_zero2
  li t1, 0x30; sb t1, 0(s0);    li t1, 1; sb t1, 64(s0)
  addi t0, s0, 128
  li t1, 0x10; sb t1, 0(t0);    li t1, 2; sb t1, 64(t0)
  addi t0, s0, 256
  li t1, 0x40; sb t1, 0(t0);    li t1, 3; sb t1, 64(t0)
  addi t0, s0, 384
  li t1, 0x20; sb t1, 0(t0);    li t1, 4; sb t1, 64(t0)
  mv a0, s0; li a1, 4; li a2, 128; li a3, 0x1400; li a4, 1; li a5, 4
  jal ra, bal_canonical_sort
  bnez a0, .Lbalsort_st_fail
  lbu t1, 64(s0);   li t2, 2; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 128; lbu t1, 64(t0); li t2, 4; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 256; lbu t1, 64(t0); li t2, 1; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 384; lbu t1, 64(t0); li t2, 3; bne t1, t2, .Lbalsort_st_fail
  li s1, 3
  mv t0, s0; li t1, 64
.Lbalsort_st_zero3:
  sd zero, 0(t0); addi t0, t0, 8; addi t1, t1, -1; bnez t1, .Lbalsort_st_zero3
  li t1, 0x10; sb t1, 19(s0);   li t1, 1; sb t1, 64(s0)
  addi t0, s0, 128
  li t1, 0x20; sb t1, 19(t0);   li t1, 2; sb t1, 64(t0)
  addi t0, s0, 256
  li t1, 0x30; sb t1, 19(t0);   li t1, 3; sb t1, 64(t0)
  addi t0, s0, 384
  li t1, 0x40; sb t1, 19(t0);   li t1, 4; sb t1, 64(t0)
  mv a0, s0; li a1, 4; li a2, 128; li a3, 0x1400; li a4, 1; li a5, 4
  jal ra, bal_canonical_sort
  bnez a0, .Lbalsort_st_fail
  lbu t1, 64(s0);   li t2, 1; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 128; lbu t1, 64(t0); li t2, 2; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 256; lbu t1, 64(t0); li t2, 3; bne t1, t2, .Lbalsort_st_fail
  addi t0, s0, 384; lbu t1, 64(t0); li t2, 4; bne t1, t2, .Lbalsort_st_fail
  li a0, 0; j .Lbalsort_st_ret
.Lbalsort_st_fail:
  mv a0, s1
.Lbalsort_st_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
