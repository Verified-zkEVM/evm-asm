node_db_lookup:
  la t0, mset_db_count; ld t6, 0(t0)   # remaining
  la t5, mset_db_data                   # record cursor
.Lndbl_loop:
  beqz t6, .Lndbl_miss
  ld t0,  0(t5); ld t1,  0(a0); bne t0, t1, .Lndbl_next
  ld t0,  8(t5); ld t1,  8(a0); bne t0, t1, .Lndbl_next
  ld t0, 16(t5); ld t1, 16(a0); bne t0, t1, .Lndbl_next
  ld t0, 24(t5); ld t1, 24(a0); bne t0, t1, .Lndbl_next
  addi t0, t5, 40; sd t0, 0(a1)        # out_ptr = record + 40
  ld t1, 32(t5);   sd t1, 0(a2)        # out_len
  li a0, 0
  ret
.Lndbl_next:
  ld t1, 32(t5)
  addi t1, t1, 7; andi t1, t1, -8; addi t1, t1, 40   # skip = 40 + roundup8(len)
  add t5, t5, t1
  addi t6, t6, -1
  j .Lndbl_loop
.Lndbl_miss:
  li a0, 1
  ret
