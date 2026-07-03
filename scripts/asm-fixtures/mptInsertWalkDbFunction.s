mpt_insert_walk_db:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a1                   # witness ptr
  mv s1, a2                   # witness_len
  mv s2, a3                   # path ptr
  mv s3, a4                   # path_len
  mv s4, a5                   # stack_out cursor
  mv s5, a6                   # meta_out
  li s9, 0                    # depth
  # EMPTY_TRIE_ROOT? (root_hash still in a0) -> case 3.
  la t2, iw_empty_trie_root
  ld t3, 0(a0); ld t4, 0(t2); bne t3, t4, .Liwd_resolve_root
  ld t3, 8(a0); ld t4, 8(t2); bne t3, t4, .Liwd_resolve_root
  ld t3, 16(a0); ld t4, 16(t2); bne t3, t4, .Liwd_resolve_root
  ld t3, 24(a0); ld t4, 24(t2); bne t3, t4, .Liwd_resolve_root
  li t5, 3; j .Liwd_empty
.Liwd_resolve_root:
  mv a2, a0                   # hash ptr = root_hash
  mv a0, s0; mv a1, s1
  la a3, iwd_ptr; la a4, iwd_len
  jal ra, mpt_node_resolve
  bnez a0, .Liwd_miss
  la t0, iwd_ptr; ld s7, 0(t0)   # absolute node ptr
  la t0, iwd_len; ld s8, 0(t0)
  li s6, 0
.Liwd_loop:
  mv a0, s7; mv a1, s8
  jal ra, mpt_node_kind
  beqz a0, .Liwd_branch
  li t0, 1; beq a0, t0, .Liwd_extension
  li t0, 2; beq a0, t0, .Liwd_leaf
  j .Liwd_parse_fail
.Liwd_branch:
  beq s6, s3, .Liwd_branch_value
  add t0, s2, s6; lbu t1, 0(t0)       # nibble
  sd s7,  0(s4)               # node_ptr ABSOLUTE
  sd s8,  8(s4); sd zero, 16(s4); sd t1, 24(s4)
  addi s4, s4, 32; addi s9, s9, 1
  mv a0, s7; mv a1, s8; mv a2, t1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  addi s6, s6, 1
  bnez a0, .Liwd_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Liwd_branch_empty
  li t2, 32
  beq t1, t2, .Liwd_branch_hash
  la t0, mw_child_offset; ld t2, 0(t0)
  add s7, s7, t2
  mv s8, t1
  j .Liwd_loop
.Liwd_branch_hash:
  # copy child hash to iwd_hash, resolve via witness+DB.
  la t0, mw_child_offset; ld t1, 0(t0); add t2, s7, t1
  la t3, iwd_hash
  ld t4,  0(t2); sd t4,  0(t3)
  ld t4,  8(t2); sd t4,  8(t3)
  ld t4, 16(t2); sd t4, 16(t3)
  ld t4, 24(t2); sd t4, 24(t3)
  mv a0, s0; mv a1, s1; la a2, iwd_hash
  la a3, iwd_ptr; la a4, iwd_len
  jal ra, mpt_node_resolve
  bnez a0, .Liwd_miss
  la t0, iwd_ptr; ld s7, 0(t0); la t0, iwd_len; ld s8, 0(t0)
  j .Liwd_loop
.Liwd_branch_empty:
  addi s4, s4, -32
  addi s9, s9, -1
  li t5, 0
  addi s6, s6, -1
  li t6, 0
  j .Liwd_record
.Liwd_branch_value:
  li t5, 5
  li t6, 0
  j .Liwd_record
.Liwd_extension:
  mv a0, s7; mv a1, s8; li a2, 0
  la a3, mw_path_offset; la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liwd_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Liwd_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0); bnez t1, .Liwd_parse_fail
  la t0, mw_nibble_count; ld t1, 0(t0)    # ext nibble count
  sub t2, s3, s6              # remaining
  mv t3, t1
  bgeu t2, t1, .Liwd_ext_lim_ok
  mv t3, t2
.Liwd_ext_lim_ok:
  la t4, mw_nibble_buf
  add t5, s2, s6
  li t6, 0
.Liwd_ext_cmp:
  beq t6, t3, .Liwd_ext_cmp_done
  add a0, t4, t6; lbu a1, 0(a0)
  add a0, t5, t6; lbu a2, 0(a0)
  bne a1, a2, .Liwd_ext_cmp_done
  addi t6, t6, 1
  j .Liwd_ext_cmp
.Liwd_ext_cmp_done:
  bne t6, t1, .Liwd_ext_split
  bgtu t1, t2, .Liwd_ext_split
  # full extension match: push it (ABS) and descend into child (item 1).
  sd s7,  0(s4); sd s8,  8(s4)
  li a1, 1; sd a1, 16(s4); sd zero, 24(s4)
  addi s4, s4, 32; addi s9, s9, 1
  add s6, s6, t1
  mv a0, s7; mv a1, s8; li a2, 1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liwd_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  la t0, mw_child_offset; ld t2, 0(t0)
  add t3, s7, t2
  li t4, 32
  beq t1, t4, .Liwd_ext_hash
  mv s7, t3
  mv s8, t1
  j .Liwd_loop
.Liwd_ext_hash:
  la t4, iwd_hash
  ld t5,  0(t3); sd t5,  0(t4)
  ld t5,  8(t3); sd t5,  8(t4)
  ld t5, 16(t3); sd t5, 16(t4)
  ld t5, 24(t3); sd t5, 24(t4)
  mv a0, s0; mv a1, s1; la a2, iwd_hash
  la a3, iwd_ptr; la a4, iwd_len
  jal ra, mpt_node_resolve
  bnez a0, .Liwd_miss
  la t0, iwd_ptr; ld s7, 0(t0); la t0, iwd_len; ld s8, 0(t0)
  j .Liwd_loop
.Liwd_ext_split:
  li t5, 2
  j .Liwd_record
.Liwd_leaf:
  mv a0, s7; mv a1, s8; li a2, 0
  la a3, mw_path_offset; la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liwd_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf; la a3, mw_nibble_count; la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Liwd_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0); li t2, 1; bne t1, t2, .Liwd_parse_fail
  la t0, mw_nibble_count; ld t1, 0(t0)    # leaf key nibble count
  sub t2, s3, s6              # remaining
  mv t3, t1
  bgeu t2, t1, .Liwd_leaf_lim_ok
  mv t3, t2
.Liwd_leaf_lim_ok:
  la t4, mw_nibble_buf
  add t5, s2, s6
  li t6, 0
.Liwd_leaf_cmp:
  beq t6, t3, .Liwd_leaf_cmp_done
  add a0, t4, t6; lbu a1, 0(a0)
  add a0, t5, t6; lbu a2, 0(a0)
  bne a1, a2, .Liwd_leaf_cmp_done
  addi t6, t6, 1
  j .Liwd_leaf_cmp
.Liwd_leaf_cmp_done:
  bne t6, t1, .Liwd_leaf_split
  bne t1, t2, .Liwd_leaf_split
  li t5, 4
  j .Liwd_record
.Liwd_leaf_split:
  li t5, 1
  j .Liwd_record
.Liwd_record:
  sd s9, 0(s5)               # depth
  sd s6, 8(s5)               # consumed
  sd t5, 16(s5)              # case
  sd s7, 24(s5)              # terminal_ptr ABSOLUTE
  sd s8, 32(s5)              # terminal_len
  sd t6, 40(s5)              # match_len
  li a0, 0
  j .Liwd_ret
.Liwd_empty:
  sd zero, 0(s5); sd zero, 8(s5); sd t5, 16(s5)
  sd zero, 24(s5); sd zero, 32(s5); sd zero, 40(s5)
  li a0, 0
  j .Liwd_ret
.Liwd_miss:
  li a0, 1
  j .Liwd_ret
.Liwd_parse_fail:
  li a0, 2
.Liwd_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
