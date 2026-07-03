mpt_set_record_walk_db:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a1                   # witness
  mv s1, a2                   # witness_len
  mv s2, a3                   # path
  mv s3, a4                   # path_len
  mv s4, a5                   # stack_out cursor
  mv s5, a6                   # meta_out
  li s9, 0                    # depth
  # root resolve (hash ptr = a0 = root_hash).
  mv a2, a0
  mv a0, s0; mv a1, s1
  la a3, mset_rw_ptr; la a4, mset_rw_len
  jal ra, mpt_node_resolve
  bnez a0, .Lmrwdb_not_found
  la t0, mset_rw_ptr; ld s7, 0(t0)   # absolute node ptr
  la t0, mset_rw_len; ld s8, 0(t0)
  li s6, 0
.Lmrwdb_loop:
  mv a0, s7; mv a1, s8
  jal ra, mpt_node_kind
  beqz a0, .Lmrwdb_branch
  li t0, 1; beq a0, t0, .Lmrwdb_extension
  li t0, 2; beq a0, t0, .Lmrwdb_leaf
  j .Lmrwdb_parse_fail
.Lmrwdb_branch:
  beq s6, s3, .Lmrwdb_branch_end
  add t0, s2, s6; lbu t1, 0(t0)       # nibble
  sd s7,  0(s4); sd s8,  8(s4); sd zero, 16(s4); sd t1, 24(s4)
  addi s4, s4, 32; addi s9, s9, 1
  mv a0, s7; mv a1, s8; mv a2, t1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  addi s6, s6, 1
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Lmrwdb_not_found
  li t2, 32; beq t1, t2, .Lmrwdb_branch_hash
  la t0, mw_child_offset; ld t2, 0(t0); add s7, s7, t2; mv s8, t1
  j .Lmrwdb_loop
.Lmrwdb_branch_hash:
  la t0, mw_child_offset; ld t1, 0(t0); add a2, s7, t1   # hash ptr
  mv a0, s0; mv a1, s1
  la a3, mset_rw_ptr; la a4, mset_rw_len
  jal ra, mpt_node_resolve
  bnez a0, .Lmrwdb_not_found
  la t0, mset_rw_ptr; ld s7, 0(t0)
  la t0, mset_rw_len; ld s8, 0(t0)
  j .Lmrwdb_loop
.Lmrwdb_branch_end:
  sd s9, 0(s5); sd s6, 8(s5); sd s7, 16(s5); sd s8, 24(s5)
  li a0, 0
  j .Lmrwdb_ret
.Lmrwdb_extension:
  mv a0, s7; mv a1, s8; li a2, 0
  la a3, mw_path_offset; la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0); bnez t1, .Lmrwdb_parse_fail
  la t0, mw_nibble_count; ld t1, 0(t0)
  add t2, s6, t1; bgtu t2, s3, .Lmrwdb_not_found
  la t2, mw_nibble_buf; add t3, s2, s6; mv t4, t1
.Lmrwdb_ext_cmp:
  beqz t4, .Lmrwdb_ext_cmp_done
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lmrwdb_not_found
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmrwdb_ext_cmp
.Lmrwdb_ext_cmp_done:
  add s6, s6, t1
  sd s7, 0(s4); sd s8, 8(s4); li t3, 1; sd t3, 16(s4); sd zero, 24(s4)
  addi s4, s4, 32; addi s9, s9, 1
  mv a0, s7; mv a1, s8; li a2, 1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  la t0, mw_child_offset; ld t2, 0(t0); add t3, s7, t2
  li t4, 32; beq t1, t4, .Lmrwdb_ext_hash
  mv s7, t3; mv s8, t1; j .Lmrwdb_loop
.Lmrwdb_ext_hash:
  mv a2, t3                   # hash ptr (= s7 + child_offset)
  mv a0, s0; mv a1, s1
  la a3, mset_rw_ptr; la a4, mset_rw_len
  jal ra, mpt_node_resolve
  bnez a0, .Lmrwdb_not_found
  la t0, mset_rw_ptr; ld s7, 0(t0)
  la t0, mset_rw_len; ld s8, 0(t0)
  j .Lmrwdb_loop
.Lmrwdb_leaf:
  mv a0, s7; mv a1, s8; li a2, 0
  la a3, mw_path_offset; la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Lmrwdb_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0); li t2, 1; bne t1, t2, .Lmrwdb_parse_fail
  la t0, mw_nibble_count; ld t1, 0(t0)
  sub t2, s3, s6; bne t1, t2, .Lmrwdb_not_found
  la t2, mw_nibble_buf; add t3, s2, s6; mv t4, t1
.Lmrwdb_leaf_cmp:
  beqz t4, .Lmrwdb_leaf_match
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lmrwdb_not_found
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmrwdb_leaf_cmp
.Lmrwdb_leaf_match:
  sd s9, 0(s5); sd s6, 8(s5); sd s7, 16(s5); sd s8, 24(s5)
  li a0, 0
  j .Lmrwdb_ret
.Lmrwdb_not_found:
  li a0, 1
  j .Lmrwdb_ret
.Lmrwdb_parse_fail:
  li a0, 2
.Lmrwdb_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
