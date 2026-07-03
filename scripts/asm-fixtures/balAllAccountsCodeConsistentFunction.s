bal_all_accounts_code_consistent:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0                   # BAL section ptr
  mv s1, a1                   # BAL section len
  mv s2, a2                   # code-effect array base
  mv s3, a3                   # record count
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbaac_fail
  mv s4, a0                   # BAL account cursor
  mv s5, a1                   # BAL account end
.Lbaac_loop:
  beq s4, s5, .Lbaac_ok
  mv a0, s4; mv a1, s5; jal ra, rlp_walk_next
  bnez a1, .Lbaac_fail
  mv s4, a0; sub s6, a0, a2; mv s7, a2   # AccountChanges ptr/len
  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init
  bnez a2, .Lbaac_fail
  jal ra, rlp_walk_next                            # item 0 = address
  bnez a1, .Lbaac_fail
  li t2, 20; bne a2, t2, .Lbaac_next   # not 20B -> skip
  sub s8, a0, a2              # addr ptr (20B BE)
  # --- find this account's code-effect by 20-byte address (variable-stride scan) ---
  mv t0, s2                    # rec_ptr = effect base
  li t1, 0                     # record index k
.Lbaac_find:
  beq t1, s3, .Lbaac_notfound  # scanned all records, none match
  li t2, 0
.Lbaac_cmp:
  li t3, 20; beq t2, t3, .Lbaac_found
  add t3, s8, t2; lbu t4, 0(t3)
  add t3, t0, t2; lbu t5, 0(t3)
  bne t4, t5, .Lbaac_adv
  addi t2, t2, 1; j .Lbaac_cmp
.Lbaac_adv:
  ld t2, 40(t0)                # code_len
  addi t2, t2, 7; andi t2, t2, -8   # roundup8(code_len)
  addi t2, t2, 48              # + header (addr 32 + has_code_change 8 + code_len 8)
  add t0, t0, t2               # rec_ptr += record size
  addi t1, t1, 1; j .Lbaac_find
.Lbaac_found:
  mv a0, s6; mv a1, s7; addi a2, t0, 32   # effect = record+32 ([has_code_change|code_len|code])
  jal ra, bal_account_code_consistent     # 0 consistent / 1 / 2 -> reject if != 0
  bnez a0, .Lbaac_fail
  j .Lbaac_next
.Lbaac_notfound:
  # No execution code-effect for this account. EEST BALs may still carry final-code
  # preimages for existing accounts, so only matched exec effects are byte-checked here.
  j .Lbaac_next
.Lbaac_next:
  j .Lbaac_loop
.Lbaac_ok:
  li a0, 0; j .Lbaac_ret
.Lbaac_fail:
  li a0, 1
.Lbaac_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)
  addi sp, sp, 80
  ret
