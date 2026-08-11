mpt_set_record_walk:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a1                   # s0 = witness ptr
  mv s1, a2                   # s1 = witness_len
  mv s2, a3                   # s2 = path_nibbles ptr
  mv s3, a4                   # s3 = path_nibbles_len
  mv s4, a5                   # s4 = stack_out cursor
  mv s5, a6                   # s5 = meta_out ptr
  li s9, 0                    # s9 = depth
  # Copy root_hash to mw_lookup_hash for the first lookup.
  la t0, mw_lookup_hash
  ld t1,  0(a0); sd t1,  0(t0)
  ld t1,  8(a0); sd t1,  8(t0)
  ld t1, 16(a0); sd t1, 16(t0)
  ld t1, 24(a0); sd t1, 24(t0)
  # First lookup of root_hash in witness.
  mv a0, s0
  mv a1, s1
  la a2, mw_lookup_hash
  la a3, mw_lookup_offset
  la a4, mw_lookup_length
  jal ra, witness_lookup_by_hash
  bnez a0, .Lmsrw_not_found
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  li s6, 0
.Lmsrw_loop:
  mv a0, s7
  mv a1, s8
  jal ra, mpt_node_kind
  beqz a0, .Lmsrw_branch
  li t0, 1; beq a0, t0, .Lmsrw_extension
  li t0, 2; beq a0, t0, .Lmsrw_leaf
  j .Lmsrw_parse_fail
.Lmsrw_branch:
  beq s6, s3, .Lmsrw_branch_end
  add t0, s2, s6              # &path[consumed]
  lbu t1, 0(t0)               # nibble (item index)
  # push record (node_offset, node_len, kind=0 branch, nibble)
  sub t2, s7, s0              # node_offset within witness
  sd t2,  0(s4)
  sd s8,  8(s4)
  sd zero, 16(s4)            # kind = 0 (branch)
  sd t1, 24(s4)
  addi s4, s4, 32
  addi s9, s9, 1
  # descend into child slot via rlp_list_nth_item.
  mv a0, s7
  mv a1, s8
  mv a2, t1                   # nibble
  la a3, mw_child_offset
  la a4, mw_child_length
  jal ra, rlp_list_nth_item
  addi s6, s6, 1
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Lmsrw_not_found   # empty slot
  li t2, 32
  beq t1, t2, .Lmsrw_branch_hash
  # Inlined (length 1..31): node = (s7 + child_offset, child_length).
  la t0, mw_child_offset; ld t2, 0(t0)
  add s7, s7, t2
  mv s8, t1
  j .Lmsrw_loop
.Lmsrw_branch_hash:
  # 32-byte hash: copy to mw_lookup_hash then lookup.
  la t0, mw_child_offset; ld t1, 0(t0)
  add t2, s7, t1
  la t3, mw_lookup_hash
  ld t4,  0(t2); sd t4,  0(t3)
  ld t4,  8(t2); sd t4,  8(t3)
  ld t4, 16(t2); sd t4, 16(t3)
  ld t4, 24(t2); sd t4, 24(t3)
  mv a0, s0
  mv a1, s1
  la a2, mw_lookup_hash
  la a3, mw_lookup_offset
  la a4, mw_lookup_length
  jal ra, witness_lookup_by_hash
  bnez a0, .Lmsrw_not_found
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  j .Lmsrw_loop
.Lmsrw_branch_end:
  # Path exhausted at a branch: this branch is the terminal node
  # (value lives in slot 16). Record it as the terminal in meta.
  sd s9, 0(s5)               # depth
  sd s6, 8(s5)               # consumed
  sub t0, s7, s0; sd t0, 16(s5) # leaf_offset
  sd s8, 24(s5)              # leaf_len
  li a0, 0
  j .Lmsrw_ret
.Lmsrw_extension:
  mv a0, s7
  mv a1, s8
  li a2, 0
  la a3, mw_path_offset
  la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf
  la a3, mw_nibble_count
  la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0)
  bnez t1, .Lmsrw_parse_fail  # node kind said extension; HP says leaf
  la t0, mw_nibble_count; ld t1, 0(t0)
  add t2, s6, t1
  bgtu t2, s3, .Lmsrw_not_found
  # Compare extension nibbles against path[consumed..].
  la t2, mw_nibble_buf
  add t3, s2, s6
  mv t4, t1
.Lmsrw_ext_cmp:
  beqz t4, .Lmsrw_ext_cmp_done
  lbu t5, 0(t2)
  lbu t6, 0(t3)
  bne t5, t6, .Lmsrw_not_found
  addi t2, t2, 1
  addi t3, t3, 1
  addi t4, t4, -1
  j .Lmsrw_ext_cmp
.Lmsrw_ext_cmp_done:
  add s6, s6, t1
  # push record (node_offset, node_len, kind=1 extension, nibble=0)
  sub t2, s7, s0
  sd t2,  0(s4)
  sd s8,  8(s4)
  li t3, 1; sd t3, 16(s4)    # kind = 1 (extension)
  sd zero, 24(s4)
  addi s4, s4, 32
  addi s9, s9, 1
  # Get item 1 (child ref).
  mv a0, s7
  mv a1, s8
  li a2, 1
  la a3, mw_child_offset
  la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  la t0, mw_child_offset; ld t2, 0(t0)
  add t3, s7, t2
  li t4, 32
  beq t1, t4, .Lmsrw_ext_hash
  # Inline child: t3 is its ptr, t1 is its length.
  mv s7, t3
  mv s8, t1
  j .Lmsrw_loop
.Lmsrw_ext_hash:
  la t4, mw_lookup_hash
  ld t5,  0(t3); sd t5,  0(t4)
  ld t5,  8(t3); sd t5,  8(t4)
  ld t5, 16(t3); sd t5, 16(t4)
  ld t5, 24(t3); sd t5, 24(t4)
  mv a0, s0
  mv a1, s1
  la a2, mw_lookup_hash
  la a3, mw_lookup_offset
  la a4, mw_lookup_length
  jal ra, witness_lookup_by_hash
  bnez a0, .Lmsrw_not_found
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  j .Lmsrw_loop
.Lmsrw_leaf:
  mv a0, s7
  mv a1, s8
  li a2, 0
  la a3, mw_path_offset
  la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf
  la a3, mw_nibble_count
  la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Lmsrw_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0)
  li t2, 1
  bne t1, t2, .Lmsrw_parse_fail
  la t0, mw_nibble_count; ld t1, 0(t0)
  sub t2, s3, s6              # remaining nibbles
  bne t1, t2, .Lmsrw_not_found
  la t2, mw_nibble_buf
  add t3, s2, s6
  mv t4, t1
.Lmsrw_leaf_cmp:
  beqz t4, .Lmsrw_leaf_match
  lbu t5, 0(t2)
  lbu t6, 0(t3)
  bne t5, t6, .Lmsrw_not_found
  addi t2, t2, 1
  addi t3, t3, 1
  addi t4, t4, -1
  j .Lmsrw_leaf_cmp
.Lmsrw_leaf_match:
  sd s9, 0(s5)               # depth
  sd s6, 8(s5)               # consumed
  sub t0, s7, s0; sd t0, 16(s5) # leaf_offset
  sd s8, 24(s5)              # leaf_len
  li a0, 0
  j .Lmsrw_ret
.Lmsrw_not_found:
  li a0, 1
  j .Lmsrw_ret
.Lmsrw_parse_fail:
  li a0, 2
.Lmsrw_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
