bal_storage_reads_in_exec_log:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                    # account addr ptr (addrHash)
  mv s1, a3                    # log base
  mv s2, a4                    # log length
  mv s5, a5                    # entry stride in bytes (128 exec log / 64 read container)
  mv a0, a1; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbsre_reject        # malformed AccountChanges -> conservative
  mv s6, a1                    # AccountChanges end
  jal ra, rlp_walk_next        # item 0 = address
  bnez a1, .Lbsre_reject
  mv a1, s6; jal ra, rlp_walk_next          # item 1 = storage_changes
  bnez a1, .Lbsre_reject
  mv a1, s6; jal ra, rlp_walk_next          # item 2 = storage_reads
  bnez a1, .Lbsre_reject
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbsre_reject
  mv s3, a0                    # storage_reads cursor
  mv s4, a1                    # storage_reads end
.Lbsre_loop:
  beq s3, s4, .Lbsre_match
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next
  bnez a1, .Lbsre_reject
  mv s3, a0
  sub t1, a0, a2                                   # content ptr (BE, MSB first)
  mv t2, a2                                        # content length
  li t0, 32; bgtu t2, t0, .Lbsre_reject
  beqz t2, .Lbsre_key_canon
  lbu t0, 0(t1); beqz t0, .Lbsre_reject             # non-canonical scalar
.Lbsre_key_canon:
  la t0, bsr_krev
  sd x0, 0(t0); sd x0, 8(t0); sd x0, 16(t0); sd x0, 24(t0)
  add t3, t1, t2; addi t3, t3, -1                   # last content byte (LSB)
  mv t4, t0                                          # dst = bsr_krev (low byte first)
  mv t5, t2
.Lbsre_rev:
  beqz t5, .Lbsre_revd
  lbu a5, 0(t3); sb a5, 0(t4); addi t3, t3, -1; addi t4, t4, 1; addi t5, t5, -1; j .Lbsre_rev
.Lbsre_revd:
  mv t2, s2
  beqz t2, .Lbsre_reject        # empty log but a read claimed
  mul t3, t2, s5; add t3, s1, t3      # past last entry
  la t6, bsr_krev
.Lbsre_scan:
  sub t3, t3, s5               # entry ptr
  ld t4, 0(t3);  ld t5, 0(s0);  bne t4, t5, .Lbsre_next
  ld t4, 8(t3);  ld t5, 8(s0);  bne t4, t5, .Lbsre_next
  ld t4, 16(t3); ld t5, 16(s0); bne t4, t5, .Lbsre_next
  ld t4, 24(t3); ld t5, 24(s0); bne t4, t5, .Lbsre_next
  ld t4, 32(t3); ld t5, 0(t6);  bne t4, t5, .Lbsre_next
  ld t4, 40(t3); ld t5, 8(t6);  bne t4, t5, .Lbsre_next
  ld t4, 48(t3); ld t5, 16(t6); bne t4, t5, .Lbsre_next
  ld t4, 56(t3); ld t5, 24(t6); bne t4, t5, .Lbsre_next
  j .Lbsre_advance              # this read slot was accessed -> next read
.Lbsre_next:
  mv t4, s1; bne t3, t4, .Lbsre_scan   # not yet at the first entry -> keep scanning
  j .Lbsre_reject               # scanned whole log, slot never accessed
.Lbsre_advance:
  j .Lbsre_loop
.Lbsre_match:
  li a0, 0
  j .Lbsre_ret
.Lbsre_reject:
  li a0, 1
.Lbsre_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
