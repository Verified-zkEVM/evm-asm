mpt_indexed_trie_root_large:
  addi sp, sp, -2016
  sd ra,   0(sp)
  sd s0,   8(sp); sd s1,  16(sp); sd s2,  24(sp); sd s3,  32(sp)
  sd s4,  40(sp); sd s5,  48(sp); sd s6,  56(sp); sd s7,  64(sp)
  sd s8,  72(sp); sd s9,  80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # value descriptors
  mv s1, a1                   # n values
  mv s2, a2                   # out root
  addi s6, sp, 160            # root branch payload buffer
  addi s7, sp, 760            # child branch payload buffer
  addi s8, sp, 1360           # branch node buffer
  li t0, 2
  bltu s1, t0, .Lilig_fallback
  li t0, 129
  bgeu s1, t0, .Lilig_fallback
  li s10, 0
.Lilig_check_loop:
  beq s10, s1, .Lilig_build_root
  slli t0, s10, 4; add t0, s0, t0
  ld t1, 8(t0)
  li t2, 56
  bltu t1, t2, .Lilig_fallback
  addi s10, s10, 1
  j .Lilig_check_loop
.Lilig_build_root:
  mv s9, s6                   # root payload cursor
  li s3, 0                    # root first-nibble slot
.Lilig_root_slot_loop:
  li t0, 16
  beq s3, t0, .Lilig_root_value_slot
  li s4, 0                    # count in this first-nibble group
  li s5, 0                    # first index in group
  li s10, 0
.Lilig_count_loop:
  beq s10, s1, .Lilig_count_done
  beqz s10, .Lilig_first_zero
  srli t1, s10, 4
  j .Lilig_first_done
.Lilig_first_zero:
  li t1, 8
.Lilig_first_done:
  bne t1, s3, .Lilig_count_next
  bnez s4, .Lilig_count_inc
  mv s5, s10
.Lilig_count_inc:
  addi s4, s4, 1
.Lilig_count_next:
  addi s10, s10, 1
  j .Lilig_count_loop
.Lilig_count_done:
  beqz s4, .Lilig_root_empty
  li t0, 1
  beq s4, t0, .Lilig_root_single
  jal ra, .Lilig_build_child
  addi a1, sp, 1968
  mv a0, s9
  jal ra, .Lilig_write_ref
  mv s9, a0
  j .Lilig_root_next
.Lilig_root_single:
  slli t0, s5, 4; add t0, s0, t0
  ld a0, 0(t0)
  ld a1, 8(t0)
  li a2, 1
  beqz s5, .Lilig_single_second_zero
  andi a3, s5, 15
  j .Lilig_single_second_done
.Lilig_single_second_zero:
  li a3, 0
.Lilig_single_second_done:
  addi a4, sp, 1968
  jal ra, mpt_indexed_large_leaf_hash
  bnez a0, .Lilig_fail
  mv a0, s9
  addi a1, sp, 1968
  jal ra, .Lilig_write_ref
  mv s9, a0
  j .Lilig_root_next
.Lilig_root_empty:
  li t0, 0x80
  sb t0, 0(s9)
  addi s9, s9, 1
.Lilig_root_next:
  addi s3, s3, 1
  j .Lilig_root_slot_loop
.Lilig_root_value_slot:
  li t0, 0x80
  sb t0, 0(s9)
  addi s9, s9, 1
  sub a1, s9, s6
  mv a0, s6
  mv a2, s2
  jal ra, .Lilig_hash_branch
  li a0, 0
  j .Lilig_ret
.Lilig_fallback:
  li a0, 2
  j .Lilig_ret
.Lilig_fail:
  li a0, 1
.Lilig_ret:
  ld ra,   0(sp)
  ld s0,   8(sp); ld s1,  16(sp); ld s2,  24(sp); ld s3,  32(sp)
  ld s4,  40(sp); ld s5,  48(sp); ld s6,  56(sp); ld s7,  64(sp)
  ld s8,  72(sp); ld s9,  80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 2016
  ret
.Lilig_build_child:
  sd s9, 128(sp)
  sd ra, 152(sp)
  mv s9, s7                   # child payload cursor
  li s4, 0                    # second nibble
.Lilig_child_slot_loop:
  li t0, 16
  beq s4, t0, .Lilig_child_value_slot
  slli s10, s3, 4
  add s10, s10, s4
  beqz s10, .Lilig_child_empty
  bgeu s10, s1, .Lilig_child_empty
  slli t0, s10, 4; add t0, s0, t0
  ld a0, 0(t0)
  ld a1, 8(t0)
  li a2, 0
  li a3, 0
  addi a4, sp, 1968
  jal ra, mpt_indexed_large_leaf_hash
  bnez a0, .Lilig_child_fail
  mv a0, s9
  addi a1, sp, 1968
  jal ra, .Lilig_write_ref
  mv s9, a0
  j .Lilig_child_next
.Lilig_child_empty:
  li t0, 0x80
  sb t0, 0(s9)
  addi s9, s9, 1
.Lilig_child_next:
  addi s4, s4, 1
  j .Lilig_child_slot_loop
.Lilig_child_value_slot:
  li t0, 0x80
  sb t0, 0(s9)
  addi s9, s9, 1
  sub a1, s9, s7
  mv a0, s7
  addi a2, sp, 1968
  jal ra, .Lilig_hash_branch
  ld s9, 128(sp)
  ld ra, 152(sp)
  ret
.Lilig_child_fail:
  ld s9, 128(sp)
  ld ra, 152(sp)
  j .Lilig_fail
.Lilig_write_ref:
  li t0, 0xa0
  sb t0, 0(a0)
  addi t0, a0, 1
  li t1, 32
.Lilig_write_ref_loop:
  lbu t2, 0(a1)
  sb t2, 0(t0)
  addi a1, a1, 1
  addi t0, t0, 1
  addi t1, t1, -1
  bnez t1, .Lilig_write_ref_loop
  addi a0, a0, 33
  ret
.Lilig_hash_branch:
  sd a0, 104(sp)
  sd a1, 112(sp)
  sd a2, 120(sp)
  sd ra, 144(sp)
  li a0, 0xc0
  ld a1, 112(sp)
  mv a2, s8
  jal ra, rlp_prefix_to_buffer
  mv t0, a0                   # prefix len
  add t1, s8, t0              # node payload cursor
  ld t2, 104(sp)              # payload src
  ld t3, 112(sp)              # remaining payload len
.Lilig_hash_copy_loop:
  beqz t3, .Lilig_hash_copy_done
  lbu t4, 0(t2)
  sb t4, 0(t1)
  addi t2, t2, 1
  addi t1, t1, 1
  addi t3, t3, -1
  j .Lilig_hash_copy_loop
.Lilig_hash_copy_done:
  ld t3, 112(sp)
  add a1, t0, t3
  mv a0, s8
  ld a2, 120(sp)
  jal ra, zkvm_keccak256
  ld ra, 144(sp)
  ret
