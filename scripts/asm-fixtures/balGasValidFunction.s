bal_gas_valid:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # BAL ptr
  mv s1, a1                   # BAL len
  mv s2, a2                   # gas_limit
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbgv_fail
  mv s3, a0                   # BAL row cursor
  mv s5, a1                   # BAL row end
  li s4, 0                    # s4 = bal_items
.Lbgv_loop:
  mv a0, s3; mv a1, s5; jal ra, rlp_walk_next
  li t0, 2; beq a1, t0, .Lbgv_done
  bnez a1, .Lbgv_fail
  mv s3, a0; sub s6, a0, a2  # account_ptr
  mv s7, a2                  # account_len
  addi s4, s4, 1             # +1 for the address
  mv a0, s6; mv a1, s7; jal ra, rlp_walk_init
  bnez a2, .Lbgv_fail
  mv s8, a0                  # account field cursor
  mv s9, a1                  # account field end
  jal ra, rlp_walk_next      # item 0 = address
  bnez a1, .Lbgv_fail
  mv s8, a0
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next # item 1 = storage_changes
  bnez a1, .Lbgv_fail
  mv s8, a0; sub a0, a0, a2; mv a1, a2
  jal ra, rlp_walk_init
  bnez a2, .Lbgv_fail
  mv s10, a0; mv s11, a1
.Lbgv_count_storage_changes:
  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next
  li t0, 2; beq a1, t0, .Lbgv_storage_reads
  bnez a1, .Lbgv_fail
  mv s10, a0; addi s4, s4, 1; j .Lbgv_count_storage_changes
.Lbgv_storage_reads:
  mv a0, s8; mv a1, s9; jal ra, rlp_walk_next # item 2 = storage_reads
  bnez a1, .Lbgv_fail
  mv s8, a0; sub a0, a0, a2; mv a1, a2
  jal ra, rlp_walk_init
  bnez a2, .Lbgv_fail
  mv s10, a0; mv s11, a1
.Lbgv_count_storage_reads:
  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next
  li t0, 2; beq a1, t0, .Lbgv_loop
  bnez a1, .Lbgv_fail
  mv s10, a0; addi s4, s4, 1; j .Lbgv_count_storage_reads
.Lbgv_done:
  # invalid iff bal_items*2000 > gas_limit
  li t0, 2000; mul t1, s4, t0
  bgtu t1, s2, .Lbgv_exceeded
  li a0, 0; j .Lbgv_ret
.Lbgv_exceeded:
  li a0, 1; j .Lbgv_ret
.Lbgv_fail:
  li a0, 2
.Lbgv_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
