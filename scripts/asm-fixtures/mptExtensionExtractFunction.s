mpt_extension_extract:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # node ptr
  mv s1, a1                   # node len
  mv s2, a2                   # nibbles out
  mv s3, a3                   # nibble_count out
  mv s4, a4                   # child_ref_ptr out
  mv s5, a5                   # child_ref_len out
  sd zero, 0(s3); sd zero, 0(s4); sd zero, 0(s5)
  # Field 0: compact path bytes.
  mv a0, s0; mv a1, s1; li a2, 0
  la a3, mee_path_off; la a4, mee_path_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lmee_parse_fail
  la t0, mee_path_len; ld t6, 0(t0)
  beqz t6, .Lmee_parse_fail
  la t0, mee_path_off; ld t5, 0(t0)
  add s6, s0, t5
  # Read prefix; reject if is_leaf bit set.
  lbu t0, 0(s6)
  srli t1, t0, 4
  andi t2, t1, 2
  bnez t2, .Lmee_not_extension
  andi t3, t1, 1
  mv t4, s2
  li t5, 0
  beqz t3, .Lmee_path_even
  andi t6, t0, 0xf
  sb t6, 0(t4)
  addi t4, t4, 1
  addi t5, t5, 1
.Lmee_path_even:
  la t0, mee_path_len; ld t1, 0(t0)
  addi t1, t1, -1
  addi t6, s6, 1
.Lmee_path_loop:
  beqz t1, .Lmee_path_done
  lbu t0, 0(t6)
  srli t2, t0, 4
  andi t3, t0, 0xf
  sb t2, 0(t4)
  sb t3, 1(t4)
  addi t4, t4, 2
  addi t5, t5, 2
  addi t6, t6, 1
  addi t1, t1, -1
  j .Lmee_path_loop
.Lmee_path_done:
  sd t5, 0(s3)
  # Field 1: child_ref bytes.
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, mee_path_off; la a4, mee_path_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lmee_parse_fail
  la t0, mee_path_off; ld t1, 0(t0)
  add t2, s0, t1
  sd t2, 0(s4)
  la t0, mee_path_len; ld t1, 0(t0)
  sd t1, 0(s5)
  li a0, 0
  j .Lmee_ret
.Lmee_not_extension:
  li a0, 2
  j .Lmee_ret
.Lmee_parse_fail:
  li a0, 1
.Lmee_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
