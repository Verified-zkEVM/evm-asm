mpt_delete_acc:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  mv s0, a1                   # witness
  mv s1, a3                   # path
  mv s2, a4                   # path_len
  mv s5, a7                   # out_root
  la t0, mdacc_witness_len; sd a2, 0(t0)
  mv a1, s0
  mv a3, s1
  mv a4, s2
  la a5, mset_stack
  la a6, mset_meta
  jal ra, mpt_delete_walk_db
  bnez a0, .Lmdacc_ret
  la t0, mset_meta; ld s6, 0(t0)   # depth
  beqz s6, .Lmdacc_empty_root
  # Bubble supports branch ancestors and extension ancestors whose child
  # remains canonical. Extension/leaf merge is handled by a follow-up.
  li t0, 0
.Lmdacc_check_loop:
  beq t0, s6, .Lmdacc_check_done
  la t1, mset_stack; slli t2, t0, 5; add t1, t1, t2
  ld t3, 16(t1); li t4, 1; bgtu t3, t4, .Lmdacc_need_collapse
  addi t0, t0, 1; j .Lmdacc_check_loop
.Lmdacc_check_done:
  # If the deepest branch would become collapsible after deleting this
  # child, stay conservative. No-collapse bubbling is canonical only when
  # the terminal branch still has at least two child refs, or has a branch
  # value plus at least one child.
  addi t0, s6, -1
  la t1, mset_stack; slli t2, t0, 5; add t1, t1, t2
  ld s3, 0(t1)                # terminal branch ptr
  ld s4, 8(t1)                # terminal branch len
  ld t3, 16(t1); bnez t3, .Lmdacc_need_collapse
  ld s7, 24(t1)               # deleted child nibble
  li s1, 0                    # i
  li s2, 0                    # non-empty child count after deletion
.Lmdacc_count_children:
  li t1, 16; beq s1, t1, .Lmdacc_count_done
  beq s1, s7, .Lmdacc_count_next
  mv a0, s3; mv a1, s4; mv a2, s1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmdacc_fail
  la t1, mw_child_length; ld t1, 0(t1)
  beqz t1, .Lmdacc_count_next
  la t2, mdacc_survivor_nibble; sd s1, 0(t2)
  addi s2, s2, 1
.Lmdacc_count_next:
  addi s1, s1, 1
  j .Lmdacc_count_children
.Lmdacc_count_done:
  mv a0, s3; mv a1, s4; li a2, 16
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmdacc_fail
  la t0, mw_child_length; ld t0, 0(t0)  # branch value length
  beqz s2, .Lmdacc_zero_children
  li t1, 1; bne s2, t1, .Lmdacc_no_collapse_needed
  beqz t0, .Lmdacc_collapse_one_child
  j .Lmdacc_no_collapse_needed
.Lmdacc_zero_children:
  bnez t0, .Lmdacc_collapse_branch_value
  j .Lmdacc_need_collapse
.Lmdacc_collapse_branch_value:
  mv a0, s3; mv a1, s4; li a2, 16
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmdacc_fail
  la t0, mw_child_offset; ld t0, 0(t0); add a2, s3, t0
  la t0, mw_child_length; ld a3, 0(t0)
  la a0, mdacc_collapsed_path; mv a1, zero
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lmdacc_fail
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  addi s7, s6, -1
  j .Lmdacc_bubble
.Lmdacc_collapse_one_child:
  la t0, mdacc_survivor_nibble; ld a2, 0(t0)
  mv a0, s3; mv a1, s4
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmdacc_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Lmdacc_need_collapse
  li t2, 32; beq t1, t2, .Lmdacc_resolve_hash_child
  la t0, mw_child_offset; ld t0, 0(t0); add t0, s3, t0
  la t2, mdacc_child_ptr; sd t0, 0(t2)
  la t2, mdacc_child_len; sd t1, 0(t2)
  j .Lmdacc_classify_child
.Lmdacc_resolve_hash_child:
  la t0, mw_child_offset; ld t0, 0(t0); add a2, s3, t0
  mv a0, s0; la t0, mdacc_witness_len; ld a1, 0(t0)
  la a3, mdacc_child_ptr; la a4, mdacc_child_len
  jal ra, mpt_node_resolve
  bnez a0, .Lmdacc_need_collapse
.Lmdacc_classify_child:
  la t0, mdacc_child_ptr; ld a0, 0(t0)
  la t0, mdacc_child_len; ld a1, 0(t0)
  jal ra, mpt_node_kind
  li t0, 2; beq a0, t0, .Lmdacc_collapse_leaf_child
  li t0, 1; beq a0, t0, .Lmdacc_collapse_extension_child
  beqz a0, .Lmdacc_collapse_branch_child
  j .Lmdacc_need_collapse
.Lmdacc_collapse_leaf_child:
  la t0, mdacc_child_ptr; ld a0, 0(t0)
  la t0, mdacc_child_len; ld a1, 0(t0)
  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len
  jal ra, mpt_leaf_extract
  bnez a0, .Lmdacc_need_collapse
  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)
  la t3, mdacc_leaf_path; addi t2, t2, 1; la t0, mdacc_leaf_path_len; ld t4, 0(t0)
.Lmdacc_cpath_cp:
  beqz t4, .Lmdacc_cpath_done
  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_cpath_cp
.Lmdacc_cpath_done:
  la t0, mdacc_leaf_path_len; ld a1, 0(t0); addi a1, a1, 1
  la a0, mdacc_collapsed_path; la t0, mdacc_leaf_value_ptr; ld a2, 0(t0); la t0, mdacc_leaf_value_len; ld a3, 0(t0)
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lmdacc_fail
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  addi s7, s6, -1
  j .Lmdacc_bubble
.Lmdacc_collapse_extension_child:
  la t0, mdacc_child_ptr; ld a0, 0(t0)
  la t0, mdacc_child_len; ld a1, 0(t0)
  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len
  jal ra, mpt_extension_extract
  bnez a0, .Lmdacc_need_collapse
  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)
  la t3, mdacc_leaf_path; addi t2, t2, 1; la t0, mdacc_leaf_path_len; ld t4, 0(t0)
.Lmdacc_epath_cp:
  beqz t4, .Lmdacc_epath_done
  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_epath_cp
.Lmdacc_epath_done:
  la t0, mdacc_leaf_value_ptr; ld t0, 0(t0)
  la t1, mdacc_leaf_value_len; ld t2, 0(t1)
  li t3, 32; bne t2, t3, .Lmdacc_ext_child_inline
  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32
.Lmdacc_ext_child_hash_cp:
  beqz t5, .Lmdacc_ext_child_hash_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_ext_child_hash_cp
.Lmdacc_ext_child_hash_done:
  li t5, 33; la t4, mset_ref_len; sd t5, 0(t4); j .Lmdacc_ext_child_ready
.Lmdacc_ext_child_inline:
  la t4, mset_ref; mv t5, t2
.Lmdacc_ext_child_inline_cp:
  beqz t5, .Lmdacc_ext_child_inline_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_ext_child_inline_cp
.Lmdacc_ext_child_inline_done:
  la t4, mset_ref_len; sd t2, 0(t4)
.Lmdacc_ext_child_ready:
  la t0, mdacc_leaf_path_len; ld a1, 0(t0); addi a1, a1, 1
  la a0, mdacc_collapsed_path; la a2, mset_ref; la t0, mset_ref_len; ld a3, 0(t0)
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_extension_node_encode
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  addi s7, s6, -1
  j .Lmdacc_bubble
.Lmdacc_collapse_branch_child:
  la t0, mdacc_survivor_nibble; ld t1, 0(t0); la t2, mdacc_collapsed_path; sb t1, 0(t2)
  mv a0, s3; mv a1, s4; mv a2, t1
  la a3, mw_child_offset; la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmdacc_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Lmdacc_need_collapse
  la t0, mw_child_offset; ld t0, 0(t0); add t0, s3, t0
  li t2, 32; bne t1, t2, .Lmdacc_branch_child_inline
  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32
.Lmdacc_branch_child_hash_cp:
  beqz t5, .Lmdacc_branch_child_hash_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_branch_child_hash_cp
.Lmdacc_branch_child_hash_done:
  la t4, mset_ref_len; li t5, 33; sd t5, 0(t4); j .Lmdacc_branch_child_ref_ready
.Lmdacc_branch_child_inline:
  la t4, mset_ref; mv t5, t1
.Lmdacc_branch_child_inline_cp:
  beqz t5, .Lmdacc_branch_child_inline_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_branch_child_inline_cp
.Lmdacc_branch_child_inline_done:
  la t4, mset_ref_len; sd t1, 0(t4)
.Lmdacc_branch_child_ref_ready:
  la a0, mdacc_collapsed_path; li a1, 1; la a2, mset_ref; la t0, mset_ref_len; ld a3, 0(t0)
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_extension_node_encode
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  addi s7, s6, -1
  j .Lmdacc_bubble
.Lmdacc_no_collapse_needed:
  # current_ref = RLP empty string/list item (0x80), the canonical empty
  # branch child reference.
  la t0, mset_ref; li t1, 0x80; sb t1, 0(t0)
  la t0, mset_ref_len; li t1, 1; sd t1, 0(t0)
  mv s7, s6                   # i = depth
.Lmdacc_bubble:
  beqz s7, .Lmdacc_root
  addi s7, s7, -1
  la t0, mset_stack; slli t1, s7, 5; add t0, t0, t1
  ld t2, 0(t0)                # node_ptr ABS
  ld t3, 8(t0)                # node_len
  ld t4, 16(t0)               # kind
  li t6, 1; beq t4, t6, .Lmdacc_bubble_extension
  bnez t4, .Lmdacc_need_collapse
  ld t5, 24(t0)               # branch nibble
  mv a0, t2; mv a1, t3; mv a2, t5
  la a3, mset_ref; la t0, mset_ref_len; ld a4, 0(t0)
  la a5, mset_node; la a6, mset_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lmdacc_fail
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  j .Lmdacc_bubble
.Lmdacc_bubble_extension:
  mv a0, t2; mv a1, t3
  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len
  jal ra, mpt_extension_extract
  bnez a0, .Lmdacc_need_collapse
  la t0, mdacc_leaf_path_len; ld t4, 0(t0); la t1, mdacc_ext_path_len; sd t4, 0(t1)
  la t2, mdacc_leaf_path; la t3, mdacc_collapsed_path
.Lmdacc_bext_path_cp:
  beqz t4, .Lmdacc_bext_path_done
  lbu t5, 0(t2); sb t5, 0(t3); addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1; j .Lmdacc_bext_path_cp
.Lmdacc_bext_path_done:
  la a0, mset_node; mv a1, s4
  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len
  jal ra, mpt_leaf_extract
  beqz a0, .Lmdacc_bubble_ext_leaf
  la a0, mset_node; mv a1, s4
  jal ra, mpt_node_kind
  li t0, 1; beq a0, t0, .Lmdacc_bubble_ext_ext
  li t0, 2; beq a0, t0, .Lmdacc_need_collapse
  li t0, 3; beq a0, t0, .Lmdacc_need_collapse
.Lmdacc_bubble_ext_rewrap:
  la a0, mdacc_collapsed_path; la t0, mdacc_ext_path_len; ld a1, 0(t0)
  la a2, mset_ref; la t0, mset_ref_len; ld a3, 0(t0)
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_extension_node_encode
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  j .Lmdacc_bubble
.Lmdacc_bubble_ext_ext:
  la a0, mset_node; mv a1, s4
  la a2, mdacc_leaf_path; la a3, mdacc_leaf_path_len; la a4, mdacc_leaf_value_ptr; la a5, mdacc_leaf_value_len
  jal ra, mpt_extension_extract
  bnez a0, .Lmdacc_need_collapse
  la t0, mdacc_ext_path_len; ld t1, 0(t0)
  la t2, mdacc_collapsed_path; add t2, t2, t1
  la t3, mdacc_leaf_path; la t0, mdacc_leaf_path_len; ld t4, 0(t0)
.Lmdacc_bext_ext_path_cp:
  beqz t4, .Lmdacc_bext_ext_path_done
  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_bext_ext_path_cp
.Lmdacc_bext_ext_path_done:
  la t0, mdacc_ext_path_len; ld t1, 0(t0); la t0, mdacc_leaf_path_len; ld t2, 0(t0); add t1, t1, t2; la t0, mdacc_ext_path_len; sd t1, 0(t0)
  la t0, mdacc_leaf_value_ptr; ld t0, 0(t0)
  la t1, mdacc_leaf_value_len; ld t2, 0(t1)
  li t3, 32; bne t2, t3, .Lmdacc_bext_ext_inline
  la t4, mset_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32
.Lmdacc_bext_ext_hash_cp:
  beqz t5, .Lmdacc_bext_ext_hash_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_bext_ext_hash_cp
.Lmdacc_bext_ext_hash_done:
  la t4, mset_ref_len; li t5, 33; sd t5, 0(t4); j .Lmdacc_bubble_ext_rewrap
.Lmdacc_bext_ext_inline:
  la t4, mset_ref; mv t5, t2
.Lmdacc_bext_ext_inline_cp:
  beqz t5, .Lmdacc_bext_ext_inline_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lmdacc_bext_ext_inline_cp
.Lmdacc_bext_ext_inline_done:
  la t4, mset_ref_len; sd t2, 0(t4); j .Lmdacc_bubble_ext_rewrap
.Lmdacc_bubble_ext_leaf:
  la t0, mdacc_ext_path_len; ld t1, 0(t0)
  la t2, mdacc_collapsed_path; add t2, t2, t1
  la t3, mdacc_leaf_path; la t0, mdacc_leaf_path_len; ld t4, 0(t0)
.Lmdacc_bext_leaf_cp:
  beqz t4, .Lmdacc_bext_leaf_done
  lbu t5, 0(t3); sb t5, 0(t2); addi t3, t3, 1; addi t2, t2, 1; addi t4, t4, -1; j .Lmdacc_bext_leaf_cp
.Lmdacc_bext_leaf_done:
  la t0, mdacc_ext_path_len; ld a1, 0(t0); la t0, mdacc_leaf_path_len; ld t1, 0(t0); add a1, a1, t1
  la a0, mdacc_collapsed_path; la t0, mdacc_leaf_value_ptr; ld a2, 0(t0); la t0, mdacc_leaf_value_len; ld a3, 0(t0)
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lmdacc_fail
  la t0, mset_node_len; ld s4, 0(t0)
  la a0, mset_node; mv a1, s4
  jal ra, node_db_append
  la a0, mset_node; mv a1, s4; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  j .Lmdacc_bubble
.Lmdacc_root:
  la a0, mset_node; mv a1, s4; mv a2, s5
  jal ra, zkvm_keccak256
  li a0, 0
  j .Lmdacc_ret
.Lmdacc_empty_root:
  la t0, iw_empty_trie_root
  ld t1, 0(t0); sd t1, 0(s5)
  ld t1, 8(t0); sd t1, 8(s5)
  ld t1, 16(t0); sd t1, 16(s5)
  ld t1, 24(t0); sd t1, 24(s5)
  li a0, 0
  j .Lmdacc_ret
.Lmdacc_need_collapse:
  li a0, 3
  j .Lmdacc_ret
.Lmdacc_fail:
  li a0, 2
.Lmdacc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
