mpt_insert_acc:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a1                   # witness ptr
  mv s1, a3                   # path ptr
  mv s2, a4                   # path_len
  mv s3, a5                   # value ptr
  mv s4, a6                   # value_len
  mv s5, a7                   # out_root
  la t0, ins_wl; sd a2, 0(t0)
  mv a1, s0
  la t0, ins_wl; ld a2, 0(t0)
  mv a3, s1
  mv a4, s2
  la a5, ins_stack
  la a6, ins_meta
  jal ra, mpt_insert_walk_db
  bnez a0, .Lacc_ret
  la t0, ins_meta
  ld s6, 0(t0)                # depth
  ld s8, 8(t0)                # consumed
  ld t1, 16(t0)               # case
  li t2, 3; beq t1, t2, .Lacc_empty
  li t2, 0; beq t1, t2, .Lacc_branch_empty
  li t2, 1; beq t1, t2, .Lacc_leaf_split
  li t2, 2; beq t1, t2, .Lacc_ext_split
  li a0, 1; j .Lacc_ret       # exists / branch-value: conservative
.Lacc_empty:
  mv a0, s1; mv a1, s2; mv a2, s3; mv a3, s4
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5
  jal ra, zkvm_keccak256
  li a0, 0; j .Lacc_ret
.Lacc_leaf_split:
  la t0, ins_meta; ld a0, 24(t0)        # terminal leaf ptr ABSOLUTE
  la t0, ins_meta; ld a1, 32(t0)
  la a2, ins_k; la a3, ins_kcount; la a4, ins_lv_ptr; la a5, ins_lv_len
  jal ra, mpt_leaf_extract
  bnez a0, .Lacc_fail
  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)
  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)
  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)
  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)
  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1
  sub a1, t1, t3; addi a1, a1, -1
  la t0, ins_lv_ptr; ld a2, 0(t0); la t0, ins_lv_len; ld a3, 0(t0)
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  la t2, ins_m; ld t3, 0(t2)
  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1
  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1
  mv a2, s3; mv a3, s4
  la a4, ins_node2; la a5, ins_node2_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lacc_fail
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  la a2, ins_ref2; la a3, ins_ref2_len
  jal ra, mpt_node_slot_encode
  la a0, ins_empty_branch; li a1, 18
  la t0, ins_niba; ld a2, 0(t0)
  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)
  la a5, ins_node; la a6, ins_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la t0, ins_nibb; ld a2, 0(t0)
  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)
  la a5, ins_node2; la a6, ins_node2_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)
  la a0, ins_node; la a1, ins_node2; mv a2, t1
  jal ra, mset_memcpy
  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lacc_ls_bubble
  la a0, ins_k; mv a1, t1
  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_extension_node_encode
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
.Lacc_ls_bubble:
  mv s7, s6
  j .Lacc_bubble
.Lacc_ext_split:
  # Split the terminal extension. Rebuild its remainder under a branch,
  # add the new leaf on the divergent nibble, optionally wrap the shared
  # prefix in a new extension, then bubble through ancestors.
  la t0, ins_meta; ld s9, 24(t0)        # terminal extension ptr ABSOLUTE
  la t0, ins_meta; ld a1, 32(t0)        # terminal extension len
  mv a0, s9; li a2, 0; la a3, mle_path_off; la a4, mle_path_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lacc_fail
  la t0, mle_path_off; ld t0, 0(t0); add a0, s9, t0
  la t0, mle_path_len; ld a1, 0(t0)
  la a2, ins_k; la a3, ins_kcount; la a4, ins_niba
  jal ra, hp_decode_nibbles
  bnez a0, .Lacc_fail
  la t0, ins_niba; ld t0, 0(t0); bnez t0, .Lacc_fail
  # child_ref from extension item 1. For hash refs, rlp_list_nth_item strips
  # the 0xa0 byte, so re-wrap 32-byte refs before feeding extension encode.
  la t0, ins_meta; ld a1, 32(t0); mv a0, s9; li a2, 1; la a3, mle_path_off; la a4, ins_lv_len
  jal ra, rlp_list_nth_item
  bnez a0, .Lacc_fail
  la t0, mle_path_off; ld t0, 0(t0); add t0, s9, t0; la t1, ins_lv_ptr; sd t0, 0(t1)
  la t1, ins_lv_len; ld t2, 0(t1); li t3, 32; bne t2, t3, .Lacc_ext_child_inline
  la t4, ins_ref; li t5, 0xa0; sb t5, 0(t4); addi t4, t4, 1; li t5, 32
.Lacc_ext_child_hash_cp:
  beqz t5, .Lacc_ext_child_hash_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lacc_ext_child_hash_cp
.Lacc_ext_child_hash_done:
  li t5, 33; la t4, ins_ref_len; sd t5, 0(t4); j .Lacc_ext_child_ready
.Lacc_ext_child_inline:
  la t4, ins_ref; mv t5, t2
.Lacc_ext_child_inline_cp:
  beqz t5, .Lacc_ext_child_inline_done
  lbu t6, 0(t0); sb t6, 0(t4); addi t0, t0, 1; addi t4, t4, 1; addi t5, t5, -1; j .Lacc_ext_child_inline_cp
.Lacc_ext_child_inline_done:
  la t4, ins_ref_len; sd t2, 0(t4)
.Lacc_ext_child_ready:
  la t0, ins_meta; ld t1, 40(t0); la t2, ins_m; sd t1, 0(t2)
  la t2, ins_k; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_niba; sd t3, 0(t4)
  add t2, s1, s8; add t2, t2, t1; lbu t3, 0(t2); la t4, ins_nibb; sd t3, 0(t4)
  # old side: if extension remainder after the divergent nibble is non-empty,
  # wrap the existing child_ref in a shorter extension; otherwise use it as-is.
  la t0, ins_kcount; ld t1, 0(t0); la t2, ins_m; ld t3, 0(t2)
  sub t4, t1, t3; addi t4, t4, -1
  beqz t4, .Lacc_ext_old_ready
  la a0, ins_k; add a0, a0, t3; addi a0, a0, 1
  mv a1, t4; la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_extension_node_encode
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
.Lacc_ext_old_ready:
  # new side leaf = leaf(path[consumed+m+1..], value).
  la t2, ins_m; ld t3, 0(t2)
  add a0, s1, s8; add a0, a0, t3; addi a0, a0, 1
  sub a1, s2, s8; sub a1, a1, t3; addi a1, a1, -1
  mv a2, s3; mv a3, s4
  la a4, ins_node2; la a5, ins_node2_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lacc_fail
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  la a2, ins_ref2; la a3, ins_ref2_len
  jal ra, mpt_node_slot_encode
  # branch with old and new children.
  la a0, ins_empty_branch; li a1, 18
  la t0, ins_niba; ld a2, 0(t0)
  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)
  la a5, ins_node; la a6, ins_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la t0, ins_nibb; ld a2, 0(t0)
  la a3, ins_ref2; la t0, ins_ref2_len; ld a4, 0(t0)
  la a5, ins_node2; la a6, ins_node2_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node2; la t0, ins_node2_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  la t0, ins_node2_len; ld t1, 0(t0); la t2, ins_node_len; sd t1, 0(t2)
  la a0, ins_node; la a1, ins_node2; mv a2, t1
  jal ra, mset_memcpy
  la t0, ins_m; ld t1, 0(t0); beqz t1, .Lacc_ext_bubble
  la a0, ins_k; mv a1, t1
  la a2, ins_ref; la t0, ins_ref_len; ld a3, 0(t0)
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_extension_node_encode
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
.Lacc_ext_bubble:
  mv s7, s6
  j .Lacc_bubble
.Lacc_branch_empty:
  add a0, s1, s8; addi a0, a0, 1
  sub a1, s2, s8; addi a1, a1, -1
  mv a2, s3; mv a3, s4
  la a4, ins_node; la a5, ins_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  la t0, ins_meta; ld a0, 24(t0)        # terminal branch ptr ABSOLUTE
  la t0, ins_meta; ld a1, 32(t0)
  add t2, s1, s8; lbu a2, 0(t2)         # nibble = path[consumed]
  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)
  la a5, ins_node; la a6, ins_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  mv s7, s6
.Lacc_bubble:
  beqz s7, .Lacc_root
  addi s7, s7, -1
  la t0, ins_stack
  slli t1, s7, 5; add t0, t0, t1
  ld t2, 0(t0)                # node_ptr ABSOLUTE
  ld t3, 8(t0)
  ld t4, 16(t0)
  ld t5, 24(t0)
  mv a0, t2; mv a1, t3        # ABSOLUTE src ptr
  beqz t4, .Lacc_k_branch
  li a2, 1; j .Lacc_k_done
.Lacc_k_branch:
  mv a2, t5
.Lacc_k_done:
  la a3, ins_ref; la t0, ins_ref_len; ld a4, 0(t0)
  la a5, ins_node; la a6, ins_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lacc_fail
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  jal ra, node_db_append
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0)
  la a2, ins_ref; la a3, ins_ref_len
  jal ra, mpt_node_slot_encode
  j .Lacc_bubble
.Lacc_root:
  la a0, ins_node; la t0, ins_node_len; ld a1, 0(t0); mv a2, s5
  jal ra, zkvm_keccak256
  li a0, 0
.Lacc_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
.Lacc_fail:
  li a0, 2
  j .Lacc_ret
