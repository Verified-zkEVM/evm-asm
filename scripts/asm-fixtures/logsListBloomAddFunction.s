logs_list_bloom_add:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                   # bloom ptr
  mv s1, a1                   # logs_rlp ptr
  mv s2, a2                   # logs_rlp len
  # ---- Count logs ----
  mv a0, s1; mv a1, s2
  la a2, llba_count
  jal ra, rlp_list_count_items
  bnez a0, .Lllba_parse_fail
  la t0, llba_count; ld s3, 0(t0)              # n_logs
  li s4, 0                                     # i
.Lllba_loop:
  bge s4, s3, .Lllba_done
  # Extract log_i bounds (full encoded item).
  mv a0, s1; mv a1, s2; mv a2, s4
  la a3, llba_offset; la a4, llba_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lllba_parse_fail
  la t0, llba_offset; ld t1, 0(t0)
  la t0, llba_length; ld t2, 0(t0)
  add a1, s1, t1                                # &log_i bytes
  mv a2, t2                                     # log_i len
  mv a0, s0                                     # bloom
  jal ra, log_bloom_add
  bnez a0, .Lllba_log_err                       # propagate child status
  addi s4, s4, 1
  j .Lllba_loop
.Lllba_done:
  li a0, 0
  j .Lllba_ret
.Lllba_parse_fail:
  li a0, 1
  j .Lllba_ret
.Lllba_log_err:
  # a0 already carries the child status (2 = address size, 3 = topic size,
  # 1 = parse fail). Pass through unchanged.
.Lllba_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 48
  ret
