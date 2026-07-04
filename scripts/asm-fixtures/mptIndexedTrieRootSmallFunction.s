mpt_indexed_trie_root_small:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # value descriptors
  mv s1, a1                   # n values
  mv s2, a2                   # out root
  li t0, 2049
  bgeu s1, t0, .Litr_fail
  beqz s1, .Litr_empty
  li t0, 1
  beq s1, t0, .Litr_one_leaf
  mv a0, s0
  mv a1, s1
  mv a2, s2
  jal ra, mpt_indexed_trie_root_large
  li t0, 2
  bne a0, t0, .Litr_ret
  li s3, 0                    # i
.Litr_build_loop:
  beq s3, s1, .Litr_build_done
  slli t0, s3, 4; add t0, s0, t0     # &value_desc[i]
  ld t1, 0(t0)                       # value ptr
  ld t2, 8(t0)                       # value len
  slli t3, s3, 3; la t4, itr_paths; add t4, t4, t3
  beqz s3, .Litr_key_zero
  li t0, 256
  bgeu s3, t0, .Litr_key_three_byte
  li t0, 128
  bgeu s3, t0, .Litr_key_two_byte
  srli t5, s3, 4
  andi t6, s3, 15
  sb t5, 0(t4); sb t6, 1(t4)
  li t0, 2
  j .Litr_key_done
.Litr_key_two_byte:
  li t5, 8; sb t5, 0(t4)
  li t5, 1; sb t5, 1(t4)
  srli t5, s3, 4
  andi t6, s3, 15
  sb t5, 2(t4); sb t6, 3(t4)
  li t0, 4
  j .Litr_key_done
.Litr_key_three_byte:
  # 256<=i<65536 -> rlp(i) = 0x82 hi lo -> nibbles [8,2, hi>>4,hi&15, lo>>4,lo&15]
  li t5, 8; sb t5, 0(t4)
  li t5, 2; sb t5, 1(t4)
  srli t5, s3, 12; andi t5, t5, 15; sb t5, 2(t4)
  srli t5, s3,  8; andi t5, t5, 15; sb t5, 3(t4)
  srli t5, s3,  4; andi t5, t5, 15; sb t5, 4(t4)
  andi t6, s3, 15; sb t6, 5(t4)
  li t0, 6
  j .Litr_key_done
.Litr_key_zero:
  li t5, 8; sb t5, 0(t4); sb zero, 1(t4)
  li t0, 2
.Litr_key_done:
  sd t0, 48(sp)              # path len
  slli t5, s3, 5; slli t6, s3, 3; add t5, t5, t6
  la s4, itr_changes; add s4, s4, t5
  sd t4, 0(s4)                # path ptr
  ld t5, 48(sp); sd t5, 8(s4) # path len
  sd t1, 16(s4)               # value ptr
  sd t2, 24(s4)               # value len
  li t5, 1; sd t5, 32(s4)     # mode = insert
  addi s3, s3, 1
  j .Litr_build_loop
.Litr_one_leaf:
  ld a0, 0(s0)                # value ptr
  ld a1, 8(s0)                # value len
  mv a2, s2                   # out root
  jal ra, mpt_indexed_trie_root_one_leaf
  j .Litr_ret
.Litr_empty:
  la t0, iw_empty_trie_root
  li t1, 32
.Litr_empty_copy:
  lbu t2, 0(t0)
  sb t2, 0(s2)
  addi t0, t0, 1
  addi s2, s2, 1
  addi t1, t1, -1
  bnez t1, .Litr_empty_copy
  li a0, 0
  j .Litr_ret
.Litr_build_done:
  la a0, iw_empty_trie_root
  la a1, itr_empty_witness
  li a2, 0
  la a3, itr_changes
  mv a4, s1
  mv a5, s2
  jal ra, mpt_state_root_ins
  j .Litr_ret
.Litr_fail:
  li a0, 1
.Litr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 56
  ret
