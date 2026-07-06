rlp_encode_uint_be:
  # Find first non-zero byte; stripped_len = src_len - leading_zeros.
  mv t0, a0
  mv t1, a1
.Lreu_skip_zero:
  beqz t1, .Lreu_all_zero
  lbu t3, 0(t0)
  bnez t3, .Lreu_have
  addi t0, t0, 1
  addi t1, t1, -1
  j .Lreu_skip_zero
.Lreu_all_zero:
  li t3, 0x80
  sb t3, 0(a2)
  li a0, 1
  ret
.Lreu_have:
  # t0 = ptr to first non-zero byte; t1 = stripped_len.
  mv t6, t1
  li t3, 1
  bne t1, t3, .Lreu_multi
  lbu t4, 0(t0)
  li t5, 0x80
  bgeu t4, t5, .Lreu_multi
  # Single-byte form.
  sb t4, 0(a2)
  li a0, 1
  ret
.Lreu_multi:
  # Short-string form: 0x80 + stripped_len, then stripped bytes.
  li t3, 0x80
  add t3, t3, t6
  sb t3, 0(a2)
  addi t4, a2, 1
  mv t1, t6
.Lreu_copy:
  beqz t1, .Lreu_done
  lbu t5, 0(t0)
  sb  t5, 0(t4)
  addi t0, t0, 1
  addi t4, t4, 1
  addi t1, t1, -1
  j .Lreu_copy
.Lreu_done:
  addi a0, t6, 1               # 1 + stripped_len
  ret
