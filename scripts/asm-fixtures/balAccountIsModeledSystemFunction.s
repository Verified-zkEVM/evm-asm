bal_account_is_modeled_system:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  jal ra, rlp_walk_init
  bnez a2, .Lbams_parse_fail
  jal ra, rlp_walk_next
  bnez a1, .Lbams_parse_fail
  li t1, 20; bne a2, t1, .Lbams_no
  sub t0, a0, a2; la t5, bams_addr_ptr; sd t0, 0(t5)
  la t1, bams_addr_2935; li t2, 20
.Lbams_cmp_2935:
  beqz t2, .Lbams_yes_2935
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbams_try_4788
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbams_cmp_2935
.Lbams_try_4788:
  la t5, bams_addr_ptr; ld t0, 0(t5); la t1, bams_addr_4788; li t2, 20
.Lbams_cmp_4788:
  beqz t2, .Lbams_yes_4788
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lbams_no
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lbams_cmp_4788
.Lbams_yes_2935:
  li a0, 1; j .Lbams_ret
.Lbams_yes_4788:
  li a0, 2; j .Lbams_ret
.Lbams_no:
  li a0, 0; j .Lbams_ret
.Lbams_parse_fail:
  li a0, 3
.Lbams_ret:
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 32
  ret
