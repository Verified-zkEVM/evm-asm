header_validate_extra_data_length:
  addi sp, sp, -16
  sd ra,  0(sp)
  li a2, 12
  la a3, hved_off
  la a4, hved_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lhved_parse_fail
  la t0, hved_len; ld t1, 0(t0)
  li t2, 32
  bgtu t1, t2, .Lhved_too_long
  li a0, 0
  j .Lhved_ret
.Lhved_too_long:
  li a0, 1
  j .Lhved_ret
.Lhved_parse_fail:
  li a0, 2
.Lhved_ret:
  ld ra,  0(sp)
  addi sp, sp, 16
  ret
