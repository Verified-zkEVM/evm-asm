mpt_set_acc:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a1                   # witness
  mv s1, a3                   # path
  mv s2, a4                   # path_len
  mv s3, a5                   # new_value
  mv s4, a6                   # new_value_len
  mv s5, a7                   # out_root
  # record-walk-db (a0=root_hash, a2=witness_len unchanged)
  mv a1, s0
  mv a3, s1
  mv a4, s2
  la a5, mset_stack
  la a6, mset_meta
  jal ra, mpt_set_record_walk_db
  bnez a0, .Lmacc_ret
  la t0, mset_meta; ld s6, 0(t0); ld s8, 8(t0)   # depth, consumed
  # re-encode leaf from path[consumed:] + new_value
  add a0, s1, s8; sub a1, s2, s8
  mv a2, s3; mv a3, s4
  la a4, mset_node; la a5, mset_node_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  bnez a0, .Lmacc_fail
  la t0, mset_node_len; ld s9, 0(t0)
  # append leaf to DB
  la a0, mset_node; mv a1, s9
  jal ra, node_db_append
  # current_ref = node_slot_encode(leaf)
  la a0, mset_node; mv a1, s9; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  mv s7, s6                   # i = depth
.Lmacc_bubble:
  beqz s7, .Lmacc_root
  addi s7, s7, -1
  la t0, mset_stack; slli t1, s7, 5; add t0, t0, t1   # &record[i]
  ld t2, 0(t0)                # node_ptr ABS
  ld t3, 8(t0)                # node_len
  ld t4, 16(t0)               # kind
  ld t5, 24(t0)               # nibble
  mv a0, t2                   # src = absolute node ptr
  mv a1, t3
  beqz t4, .Lmacc_k_branch
  li a2, 1
  j .Lmacc_k_done
.Lmacc_k_branch:
  mv a2, t5
.Lmacc_k_done:
  la a3, mset_ref; la t0, mset_ref_len; ld a4, 0(t0)
  la a5, mset_node; la a6, mset_node_len
  jal ra, mpt_splice_slot
  bnez a0, .Lmacc_fail
  la t0, mset_node_len; ld s9, 0(t0)
  # append new node to DB
  la a0, mset_node; mv a1, s9
  jal ra, node_db_append
  # current_ref = node_slot_encode(new node)
  la a0, mset_node; mv a1, s9; la a2, mset_ref; la a3, mset_ref_len
  jal ra, mpt_node_slot_encode
  j .Lmacc_bubble
.Lmacc_root:
  la a0, mset_node; mv a1, s9; mv a2, s5
  jal ra, zkvm_keccak256
  li a0, 0
.Lmacc_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
.Lmacc_fail:
  li a0, 2
  j .Lmacc_ret
