bal_all_accounts_code_covers:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0                   # BAL section ptr
  mv s1, a1                   # BAL section len
  mv s2, a2                   # code-effect array base
  mv s3, a3                   # record count
  mv s5, s2                    # rec_ptr = effect base
  li s6, 0                     # record index k
.Lbacov_eloop:
  beq s6, s3, .Lbacov_ok
  ld t0, 32(s5); beqz t0, .Lbacov_advance   # has_code_change == 0 -> no obligation
  # changed: scan BAL accounts for one whose item-0 address == effect record address (s5+0)
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbacov_fail
  mv s7, a0                    # BAL cursor
  mv s8, a1                    # BAL end
.Lbacov_sloop:
  beq s7, s8, .Lbacov_fail     # scanned all, no BAL account -> reject (omitted created/destroyed account)
  mv a0, s7; mv a1, s8; jal ra, rlp_walk_next
  bnez a1, .Lbacov_fail        # malformed BAL list -> reject
  mv s7, a0; sub t2, a0, a2    # AccountChanges ptr/len = t2/a2
  mv a0, t2; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbacov_fail
  jal ra, rlp_walk_next                              # item 0 = address
  bnez a1, .Lbacov_fail        # malformed account -> reject
  li t2, 20; bne a2, t2, .Lbacov_sadv   # not 20B -> not a match
  sub t2, a0, a2               # BAL addr ptr (20B BE)
  li t3, 0
.Lbacov_acmp:
  li t4, 20; beq t3, t4, .Lbacov_advance   # all 20 equal -> account present -> obligation met
  add t4, s5, t3; lbu t5, 0(t4)            # effect record address byte
  add t4, t2, t3; lbu t6, 0(t4)            # BAL address byte
  bne t5, t6, .Lbacov_sadv
  addi t3, t3, 1; j .Lbacov_acmp
.Lbacov_sadv:
  j .Lbacov_sloop
.Lbacov_advance:
  ld t0, 40(s5); addi t0, t0, 7; andi t0, t0, -8; addi t0, t0, 48   # record size = 48 + roundup8(code_len)
  add s5, s5, t0
  addi s6, s6, 1; j .Lbacov_eloop
.Lbacov_ok:
  li a0, 0; j .Lbacov_ret
.Lbacov_fail:
  li a0, 1
.Lbacov_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 96
  ret
