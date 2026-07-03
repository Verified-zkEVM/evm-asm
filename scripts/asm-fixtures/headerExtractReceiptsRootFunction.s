header_extract_receipts_root:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  mv s1, a1
  mv s2, a2
  mv a0, s0; mv a1, s1; li a2, 5
  la a3, herr_offset; la a4, herr_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lherr_parse_fail
  la t0, herr_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lherr_size_fail
  la t0, herr_offset; ld t1, 0(t0)
  add t3, s0, t1
  ld t4,  0(t3); sd t4,  0(s2)
  ld t4,  8(t3); sd t4,  8(s2)
  ld t4, 16(t3); sd t4, 16(s2)
  ld t4, 24(t3); sd t4, 24(s2)
  li a0, 0
  j .Lherr_ret
.Lherr_parse_fail:
  li a0, 1
  j .Lherr_ret
.Lherr_size_fail:
  li a0, 2
.Lherr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
