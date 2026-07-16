account_is_eip161_empty:
  addi sp, sp, -40
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # account_ptr
  mv s1, a1                   # account_len
  mv s2, a2                   # is_empty out
  sd zero, 0(s2)
  # ---- Field 0: nonce ---- BE-decode and check == 0
  mv a0, s0; mv a1, s1; li a2, 0
  la a3, aie_offset; la a4, aie_length
  jal ra, rlp_list_nth_item
  bnez a0, .Laie_fail
  la t0, aie_length; ld t1, 0(t0)
  li t2, 8
  bgtu t1, t2, .Laie_fail      # nonce > 8 bytes
  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3
  li t2, 0
.Laie_nloop:
  beqz t1, .Laie_ndone
  slli t2, t2, 8
  lbu t4, 0(t3)
  or t2, t2, t4
  addi t3, t3, 1
  addi t1, t1, -1
  j .Laie_nloop
.Laie_ndone:
  bnez t2, .Laie_not_empty     # nonce != 0
  # ---- Field 1: balance ---- check all bytes == 0
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, aie_offset; la a4, aie_length
  jal ra, rlp_list_nth_item
  bnez a0, .Laie_fail
  la t0, aie_length; ld t1, 0(t0)
  li t2, 32
  bgtu t1, t2, .Laie_fail      # balance > 32 bytes
  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3
.Laie_bloop:
  beqz t1, .Laie_bdone
  lbu t4, 0(t3)
  bnez t4, .Laie_not_empty     # balance non-zero byte
  addi t3, t3, 1
  addi t1, t1, -1
  j .Laie_bloop
.Laie_bdone:
  # ---- Field 3: code_hash ---- length == 32 and bytes match
  mv a0, s0; mv a1, s1; li a2, 3
  la a3, aie_offset; la a4, aie_length
  jal ra, rlp_list_nth_item
  bnez a0, .Laie_fail
  la t0, aie_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Laie_sizefail
  la t0, aie_offset; ld t3, 0(t0); add t3, s0, t3
  la t6, aie_empty_code_hash
.Laie_hloop:
  lbu t5, 0(t3); lbu t4, 0(t6); bne t5, t4, .Laie_not_empty
  addi t3, t3, 1; addi t6, t6, 1; addi t1, t1, -1
  bnez t1, .Laie_hloop
  nop; nop; nop; nop; nop
  li t0, 1
  sd t0, 0(s2)
  li a0, 0
  j .Laie_ret
.Laie_not_empty:
  sd zero, 0(s2)
  li a0, 0
  j .Laie_ret
.Laie_fail:
  li a0, 1
  j .Laie_ret
.Laie_sizefail:
  li a0, 2
.Laie_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 40
  ret
