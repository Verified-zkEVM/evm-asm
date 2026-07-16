header_extract_logs_bloom:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # header_rlp ptr
  mv s1, a1                   # header_rlp len
  mv s2, a2                   # output bloom ptr
  # ---- Field 6: logs_bloom (must be 256 bytes) ----
  mv a0, s0; mv a1, s1; li a2, 6
  la a3, helb_offset; la a4, helb_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lhelb_fail
  la t0, helb_length; ld t1, 0(t0)
  li t2, 256
  bne t1, t2, .Lhelb_size_fail
  la t0, helb_offset; ld t1, 0(t0)
  add t3, s0, t1                              # src ptr
  mv t4, s2                                   # dst ptr
  li t5, 256
.Lhelb_loop:
  beqz t5, .Lhelb_done
  lbu t6, 0(t3)
  sb t6, 0(t4)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Lhelb_loop
.Lhelb_done:
  li a0, 0
  j .Lhelb_ret
.Lhelb_fail:
  li a0, 1
  j .Lhelb_ret
.Lhelb_size_fail:
  li a0, 2
.Lhelb_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
