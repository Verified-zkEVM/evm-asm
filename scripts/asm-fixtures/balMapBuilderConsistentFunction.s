bal_map_builder_consistent:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  la t0, account_writes_count; ld s0, 0(t0); li s1, 0
.Lbmb_bal:
  bgeu s1, s0, .Lbmb_nonce
  slli t1, s1, 7; li t2, 0xbdb80000; add t2, t2, t1
  mv a0, t2; li a1, 1; jal ra, bal_map_final_value_matches; bnez a0, .Lbmb_fail
  addi s1, s1, 1; j .Lbmb_bal
.Lbmb_nonce:
  la t0, account_writes_count; ld s0, 0(t0); li s1, 0
.Lbmb_non:
  bgeu s1, s0, .Lbmb_code
  slli t1, s1, 7; li t2, 0xbdb80000; add t2, t2, t1
  mv a0, t2; li a1, 2; jal ra, bal_map_final_value_matches; bnez a0, .Lbmb_fail
  addi s1, s1, 1; j .Lbmb_non
.Lbmb_code:
  la t0, account_writes_count; ld s0, 0(t0); li s1, 0
.Lbmb_cod:
  bgeu s1, s0, .Lbmb_ok
  slli t1, s1, 7; li t2, 0xbdb80000; add t2, t2, t1
  mv a0, t2; li a1, 3; jal ra, bal_map_final_value_matches; bnez a0, .Lbmb_fail
  addi s1, s1, 1; j .Lbmb_cod
.Lbmb_ok:
  li a0, 0; j .Lbmb_ret
.Lbmb_fail:
  li a0, 1
.Lbmb_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); addi sp, sp, 32; ret
