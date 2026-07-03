rlp_list_encoded_size:
  li t0, 56; bgeu a0, t0, .Lrles_long
  addi a0, a0, 1; ret
.Lrles_long:
  mv t0, a0; li t1, 0
.Lrles_len_loop:
  beqz t0, .Lrles_len_done
  srli t0, t0, 8; addi t1, t1, 1; j .Lrles_len_loop
.Lrles_len_done:
  add a0, a0, t1; addi a0, a0, 1; ret
