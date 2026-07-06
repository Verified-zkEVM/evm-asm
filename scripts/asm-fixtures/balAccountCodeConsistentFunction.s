bal_account_code_consistent:
  addi sp, sp, -32
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # AccountChanges ptr
  mv s1, a2                   # exec code effect ptr
  la s2, bacc_finals          # 88-byte finals scratch
  mv a2, s2                   # finals out = scratch (a0/a1 still AccountChanges ptr/len)
  jal ra, bal_account_nonstorage_finals
  bnez a0, .Lbacc_parsefail   # BAL parse failure -> 2
  ld t0, 56(s2)               # bal_declared = has_code
  ld t1, 0(s1)                # exec_changed = has_code_change
  bnez t1, .Lbacc_exec_changed
  # exec did NOT change code
  beqz t0, .Lbacc_ok          # BAL silent too -> consistent
  j .Lbacc_bad                # BAL declares a code change exec didn't make -> reject
.Lbacc_exec_changed:
  beqz t0, .Lbacc_bad         # exec changed code but BAL silent -> reject
  # both declare: lengths then bytes must match
  ld t2, 72(s2)               # BAL code_len
  ld t3, 8(s1)                # exec code_len
  bne t2, t3, .Lbacc_bad
  ld t4, 64(s2); add t4, s0, t4   # BAL code ptr = AccountChanges + code_off
  addi t5, s1, 16             # exec code ptr
.Lbacc_cmp:
  beqz t2, .Lbacc_ok
  lbu t6, 0(t4); lbu a0, 0(t5); bne t6, a0, .Lbacc_bad
  addi t4, t4, 1; addi t5, t5, 1; addi t2, t2, -1; j .Lbacc_cmp
.Lbacc_ok:
  li a0, 0; j .Lbacc_ret
.Lbacc_bad:
  li a0, 1; j .Lbacc_ret
.Lbacc_parsefail:
  li a0, 2
.Lbacc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
