rlp_bytes_encoded_size:
  li t0, 1
  bne a1, t0, .Lrbes_not_single
  lbu t1, 0(a0); li t2, 0x80; bltu t1, t2, .Lrbes_single_raw
.Lrbes_not_single:
  li t0, 56; bgeu a1, t0, .Lrbes_long
  addi a0, a1, 1; ret
.Lrbes_single_raw:
  li a0, 1; ret
.Lrbes_long:
  mv t0, a1; li t1, 0
.Lrbes_len_loop:
  beqz t0, .Lrbes_len_done
  srli t0, t0, 8; addi t1, t1, 1; j .Lrbes_len_loop
.Lrbes_len_done:
  add a0, a1, t1; addi a0, a0, 1; ret
