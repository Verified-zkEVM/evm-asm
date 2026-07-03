bal_find_account_by_address:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a0                    # BAL section ptr
  mv s1, a1                    # BAL section len
  mv s2, a2                    # target address ptr
  mv s3, a3                    # out account ptr cell
  mv s4, a4                    # out account len cell
  mv a0, s0; mv a1, s1
  jal ra, rlp_walk_init
  bnez a2, .Lbfa_parse_err
  mv s5, a0                    # cursor
  mv s6, a1                    # end
  mv s7, zero                  # i
.Lbfa_loop:
  mv a0, s5; mv a1, s6; jal ra, rlp_walk_next
  li t0, 2; beq a1, t0, .Lbfa_notfound
  bnez a1, .Lbfa_parse_err
  mv s5, a0
  sub s8, a0, a2                # account ptr
  mv s9, a2                     # account len
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_init
  bnez a2, .Lbfa_next
  jal ra, rlp_walk_next
  bnez a1, .Lbfa_next
  li t4, 20; bne a2, t4, .Lbfa_next
  sub t1, a0, a2                # address bytes ptr
  mv t3, s2; li t4, 20
.Lbfa_cmp:
  beqz t4, .Lbfa_match
  lbu t5, 0(t1); lbu t6, 0(t3); bne t5, t6, .Lbfa_next
  addi t1, t1, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lbfa_cmp
.Lbfa_match:
  la t6, bfa_index; sd s7, 0(t6)
  sd s8, 0(s3)
  sd s9, 0(s4)
  li a0, 0; j .Lbfa_ret
.Lbfa_next:
  addi s7, s7, 1; j .Lbfa_loop
.Lbfa_notfound:
  li a0, 1; j .Lbfa_ret
.Lbfa_parse_err:
  li a0, 2
.Lbfa_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
