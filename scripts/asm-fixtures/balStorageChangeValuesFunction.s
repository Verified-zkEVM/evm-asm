bal_storage_change_values:
  addi sp, sp, -128
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  sd s7, 64(sp); sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                    # account ptr
  mv s1, a1                    # account len
  mv s2, a2                    # out keys ptr
  la t0, bscv_vptr; sd a3, 0(t0)   # out values ptr (data label, s-regs are full)
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbscv_fail
  mv s3, a1                    # account end
  jal ra, rlp_walk_next        # item 0 = address
  bnez a1, .Lbscv_fail
  mv a1, s3; jal ra, rlp_walk_next                  # item 1 = storage_changes
  bnez a1, .Lbscv_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbscv_fail
  mv s3, a0                    # storage_changes cursor
  mv s4, a1                    # storage_changes end
  mv s5, zero                  # count written
.Lbscv_loop:
  beq s3, s4, .Lbscv_done
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_next
  bnez a1, .Lbscv_fail
  mv s3, a0; sub s7, a0, a2; mv s8, a2              # entry ptr/len
  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init
  bnez a2, .Lbscv_fail
  mv s9, a1                    # entry end
  jal ra, rlp_walk_next        # key = item 0
  bnez a1, .Lbscv_fail
  mv s10, a0                   # cursor after key
  sub t1, a0, a2               # key bytes ptr
  mv t4, a2                    # key byte len
  li t5, 32; bgtu t4, t5, .Lbscv_fail
  slli t0, s5, 5; add t6, s2, t0                    # key dst base
  mv t0, t6; li t5, 32
.Lbscv_kzero:
  beqz t5, .Lbscv_kzdone
  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbscv_kzero
.Lbscv_kzdone:
  li t5, 32; sub t5, t5, t4; add t0, t6, t5         # dst = base + (32 - klen)
.Lbscv_kcopy:
  beqz t4, .Lbscv_kcdone
  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbscv_kcopy
.Lbscv_kcdone:
  mv a0, s10; mv a1, s9; jal ra, rlp_walk_next
  bnez a1, .Lbscv_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbscv_fail
  beq a0, a1, .Lbscv_fail       # no tuples -> malformed
  mv s10, a0; mv s11, a1        # value_list cursor/end
.Lbscv_vlist_loop:
  beq s10, s11, .Lbscv_vlist_done
  mv a0, s10; mv a1, s11; jal ra, rlp_walk_next
  bnez a1, .Lbscv_fail
  mv s10, a0; sub s7, a0, a2; mv s8, a2             # last tuple ptr/len
  j .Lbscv_vlist_loop
.Lbscv_vlist_done:
  mv a0, s7; mv a1, s8; jal ra, rlp_walk_init
  bnez a2, .Lbscv_fail
  mv s9, a1                                        # tuple end
  jal ra, rlp_walk_next                            # item 0 = tx_index
  bnez a1, .Lbscv_fail
  mv a1, s9; jal ra, rlp_walk_next                 # item 1 = new_value
  bnez a1, .Lbscv_fail
  sub t1, a0, a2                                   # new_value bytes ptr
  mv t4, a2                                        # new_value byte len
  li t5, 32; bgtu t4, t5, .Lbscv_fail
  la t0, bscv_vptr; ld t6, 0(t0); slli t0, s5, 5; add t6, t6, t0   # value dst base
  mv t0, t6; li t5, 32
.Lbscv_vzero:
  beqz t5, .Lbscv_vzdone
  sb zero, 0(t0); addi t0, t0, 1; addi t5, t5, -1; j .Lbscv_vzero
.Lbscv_vzdone:
  li t5, 32; sub t5, t5, t4; add t0, t6, t5
.Lbscv_vcopy:
  beqz t4, .Lbscv_vcdone
  lbu t5, 0(t1); sb t5, 0(t0); addi t1, t1, 1; addi t0, t0, 1; addi t4, t4, -1; j .Lbscv_vcopy
.Lbscv_vcdone:
  addi s5, s5, 1; j .Lbscv_loop
.Lbscv_done:
  mv a0, s5
  j .Lbscv_ret
.Lbscv_fail:
  li a0, 0
.Lbscv_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  ld s7, 64(sp); ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 128
  ret
