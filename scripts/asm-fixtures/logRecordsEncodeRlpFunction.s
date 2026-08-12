log_records_encode_rlp:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # descriptor cursor
  mv s1, a1                   # remaining logs
  mv s2, a2                   # data base
  mv s3, a3                   # meta cursor
  mv s4, a4                   # out ptr
  mv s5, a5                   # out cap
  mv s6, a6                   # out len ptr
  sd zero, 0(s6)
  li s7, 0                    # logs payload cursor (into lrr_payload)
.Llrr_log_loop:
  beqz s1, .Llrr_finish
  la t0, lrr_addr_be
  addi t1, s0, 8
  li t2, 0
.Llrr_addr_copy:
  li t3, 20; beq t2, t3, .Llrr_addr_done
  add t3, t1, t2
  lbu t4, 0(t3)
  add t3, t0, t2
  sb t4, 0(t3)
  addi t2, t2, 1
  j .Llrr_addr_copy
.Llrr_addr_done:
  la a0, lrr_addr_be; li a1, 20; la a2, lrr_inner; la a3, lrr_len
  jal ra, rlp_encode_bytes
  la t0, lrr_len; ld s8, 0(t0)        # s8 = inner cursor
  ld s9, 0(s0)                # topic_count
  li t0, 4; bgtu s9, t0, .Llrr_malformed
  li s10, 0                   # topic index
  li s11, 0                   # topics payload cursor
.Llrr_topic_loop:
  beq s10, s9, .Llrr_topics_done
  slli t0, s10, 5
  addi t1, s0, 32
  add t1, t1, t0              # topic slot (LE)
  la t0, lrr_topic_be
  li t2, 0
.Llrr_topic_rev:
  li t3, 32; beq t2, t3, .Llrr_topic_rev_done
  li t3, 31; sub t3, t3, t2
  add t3, t1, t3
  lbu t4, 0(t3)
  add t3, t0, t2
  sb t4, 0(t3)
  addi t2, t2, 1
  j .Llrr_topic_rev
.Llrr_topic_rev_done:
  la a0, lrr_topic_be; li a1, 32
  la a2, lrr_topics; add a2, a2, s11
  la a3, lrr_len
  jal ra, rlp_encode_bytes
  la t0, lrr_len; ld t1, 0(t0)
  add s11, s11, t1
  addi s10, s10, 1
  j .Llrr_topic_loop
.Llrr_topics_done:
  mv a0, s11
  la a1, lrr_inner; add a1, a1, s8
  la a2, lrr_len
  jal ra, rlp_encode_list_prefix
  la t0, lrr_len; ld t1, 0(t0)
  add s8, s8, t1
  la t0, lrr_topics
  la t1, lrr_inner; add t1, t1, s8
  mv t2, s11
.Llrr_topics_copy:
  beqz t2, .Llrr_topics_copied
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Llrr_topics_copy
.Llrr_topics_copied:
  add s8, s8, s11
  ld s10, 8(s3)               # data len
  li t0, 1; bne s10, t0, .Llrr_data_hdr
  ld t1, 0(s3)
  add t1, s2, t1
  lbu t2, 0(t1)
  li t3, 0x80; bgeu t2, t3, .Llrr_data_hdr
  li s11, 0                   # single low byte: no header
  j .Llrr_data_hdr_done
.Llrr_data_hdr:
  li t0, 56
  bltu s10, t0, .Llrr_data_short
  la t1, lrr_dhdr
  li t2, 0                    # len-of-len
  mv t3, s10
.Llrr_data_lol:
  beqz t3, .Llrr_data_lol_done
  srli t3, t3, 8
  addi t2, t2, 1
  j .Llrr_data_lol
.Llrr_data_lol_done:
  li t4, 0xb7
  add t4, t4, t2
  sb t4, 0(t1)
  mv t3, t2
.Llrr_data_lenbytes:
  beqz t3, .Llrr_data_long_done
  addi t3, t3, -1
  slli t4, t3, 3
  srl t4, s10, t4
  andi t4, t4, 0xff
  sub t5, t2, t3
  add t5, t1, t5
  sb t4, 0(t5)
  j .Llrr_data_lenbytes
.Llrr_data_long_done:
  addi s11, t2, 1             # header bytes = 1 + len-of-len
  j .Llrr_data_hdr_done
.Llrr_data_short:
  la t1, lrr_dhdr
  li t4, 0x80
  add t4, t4, s10
  sb t4, 0(t1)
  li s11, 1
.Llrr_data_hdr_done:
  add t0, s8, s11
  add t0, t0, s10
  mv a0, t0
  la a1, lrr_payload; add a1, a1, s7
  la a2, lrr_len
  jal ra, rlp_encode_list_prefix
  la t0, lrr_len; ld t1, 0(t0)
  add s7, s7, t1
  la t0, lrr_inner
  la t1, lrr_payload; add t1, t1, s7
  mv t2, s8
.Llrr_inner_copy:
  beqz t2, .Llrr_inner_copied
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Llrr_inner_copy
.Llrr_inner_copied:
  add s7, s7, s8
  la t0, lrr_dhdr
  la t1, lrr_payload; add t1, t1, s7
  mv t2, s11
.Llrr_dhdr_copy:
  beqz t2, .Llrr_dhdr_copied
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Llrr_dhdr_copy
.Llrr_dhdr_copied:
  add s7, s7, s11
  ld t0, 0(s3)                # data offset
  add t0, s2, t0
  la t1, lrr_payload; add t1, t1, s7
  mv t2, s10
  add t3, s7, t2
  li t4, 2095652
  bgtu t3, t4, .Llrr_overflow
.Llrr_data_copy:
  beqz t2, .Llrr_data_copied
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Llrr_data_copy
.Llrr_data_copied:
  add s7, s7, s10
  ld t0, 0(s0); slli t0, t0, 5; addi t0, t0, 32   # reclen = 32 + 32*topic_count
  add s0, s0, t0             # advance packed descriptor
  addi s3, s3, 24            # 24 B meta stride
  addi s1, s1, -1
  j .Llrr_log_loop
.Llrr_finish:
  li t0, 9
  bgtu t0, s5, .Llrr_overflow
  mv a0, s7
  mv a1, s4
  la a2, lrr_len
  jal ra, rlp_encode_list_prefix
  la t0, lrr_len; ld t1, 0(t0)
  add t2, t1, s7
  bgtu t2, s5, .Llrr_overflow
  sd t2, 0(s6)
  add t3, s4, t1
  la t4, lrr_payload
  mv t5, s7
.Llrr_out_copy:
  beqz t5, .Llrr_ok
  lbu t6, 0(t4)
  sb t6, 0(t3)
  addi t3, t3, 1
  addi t4, t4, 1
  addi t5, t5, -1
  j .Llrr_out_copy
.Llrr_ok:
  li a0, 0
  j .Llrr_ret
.Llrr_malformed:
  li a0, 1
  j .Llrr_ret
.Llrr_overflow:
  li a0, 2
.Llrr_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
