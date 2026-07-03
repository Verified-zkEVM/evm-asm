mpt_branch_child:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                  # node ptr
  mv s1, a1                  # node_len
  mv s2, a2                  # nibble
  mv s3, a3                  # out ptr
  li t0, 16
  bgeu s2, t0, .Lmbc_fail    # nibble ≥ 16 → out of range
  # Call rlp_list_nth_item(node, len, nibble, &mbc_offset, &mbc_length).
  mv a0, s0; mv a1, s1; mv a2, s2
  la a3, mbc_offset
  la a4, mbc_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmbc_fail
  la t0, mbc_length
  ld t1, 0(t0)
  beqz t1, .Lmbc_empty       # length 0 ⇒ empty slot
  li t0, 32
  bne t1, t0, .Lmbc_inlined  # length != 32 ⇒ inlined
  # Hash slot: copy 32 bytes from node + offset to out.
  la t0, mbc_offset
  ld t2, 0(t0)
  add t2, s0, t2             # src
  ld t3,  0(t2); sd t3,  0(s3)
  ld t3,  8(t2); sd t3,  8(s3)
  ld t3, 16(t2); sd t3, 16(s3)
  ld t3, 24(t2); sd t3, 24(s3)
  li a0, 0
  j .Lmbc_ret
.Lmbc_empty:
  sd zero,  0(s3); sd zero,  8(s3)
  sd zero, 16(s3); sd zero, 24(s3)
  li a0, 1
  j .Lmbc_ret
.Lmbc_inlined:
  # Length 1..31. Zero the output, then byte-copy `length` bytes.
  sd zero,  0(s3); sd zero,  8(s3)
  sd zero, 16(s3); sd zero, 24(s3)
  la t0, mbc_offset
  ld t2, 0(t0)
  add t2, s0, t2             # src cursor
  mv t3, s3                  # dst cursor
.Lmbc_inline_cp:
  beqz t1, .Lmbc_inline_done
  lbu t4, 0(t2)
  sb  t4, 0(t3)
  addi t2, t2, 1
  addi t3, t3, 1
  addi t1, t1, -1
  j .Lmbc_inline_cp
.Lmbc_inline_done:
  li a0, 2
  j .Lmbc_ret
.Lmbc_fail:
  sd zero,  0(s3); sd zero,  8(s3)
  sd zero, 16(s3); sd zero, 24(s3)
  li a0, 3
.Lmbc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
