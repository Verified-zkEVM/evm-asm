mpt_insert_walk:
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
  # EMPTY_TRIE_ROOT? -> case 3 (whole trie is a single new leaf).
  la t2, iw_empty_trie_root
  ld t3, 0(t0); ld t4, 0(t2); bne t3, t4, .Liw_lookup_root
  ld t3, 8(t0); ld t4, 8(t2); bne t3, t4, .Liw_lookup_root
  ld t3, 16(t0); ld t4, 16(t2); bne t3, t4, .Liw_lookup_root
  ld t3, 24(t0); ld t4, 24(t2); bne t3, t4, .Liw_lookup_root
  li t5, 3; j .Liw_empty
.Liw_lookup_root:
  mv a0, s0
  mv a1, s1
  la a2, mw_lookup_hash
  la a3, mw_lookup_offset
  la a4, mw_lookup_length
  jal ra, witness_lookup_by_hash
  bnez a0, .Liw_miss
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  li s6, 0
.Liw_loop:
  mv a0, s7
  mv a1, s8
  jal ra, mpt_node_kind
  beqz a0, .Liw_branch
  li t0, 1; beq a0, t0, .Liw_extension
  li t0, 2; beq a0, t0, .Liw_leaf
  j .Liw_parse_fail
.Liw_branch:
  beq s6, s3, .Liw_branch_value
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
  bnez a0, .Liw_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  beqz t1, .Liw_branch_empty  # empty slot -> insert point
  li t2, 32
  beq t1, t2, .Liw_branch_hash
  # Inlined (length 1..31): node = (s7 + child_offset, child_length).
  la t0, mw_child_offset; ld t2, 0(t0)
  add s7, s7, t2
  mv s8, t1
  j .Liw_loop
.Liw_branch_hash:
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
  bnez a0, .Liw_miss
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  j .Liw_loop
.Liw_branch_empty:
  # The branch (just pushed) is the terminal: un-push it; ancestors = s9-1.
  addi s4, s4, -32
  addi s9, s9, -1
  li t5, 0                    # case 0 BRANCH_EMPTY_SLOT
  addi s6, s6, -1             # consumed = ancestors' nibbles (drop branch nibble)
  li t6, 0                    # match_len = 0
  j .Liw_record
.Liw_branch_value:
  # Path exhausted at a branch (value slot 16). Defensive (not for 64-nibble
  # account paths). The branch is the terminal; it is NOT on the stack.
  li t5, 5                    # case 5 BRANCH_VALUE
  li t6, 0
  j .Liw_record
.Liw_extension:
  mv a0, s7
  mv a1, s8
  li a2, 0
  la a3, mw_path_offset
  la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liw_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf
  la a3, mw_nibble_count
  la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Liw_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0)
  bnez t1, .Liw_parse_fail    # node kind said extension; HP says leaf
  la t0, mw_nibble_count; ld t1, 0(t0)    # t1 = ext nibble count
  # common prefix of ext nibbles (mw_nibble_buf) vs path[consumed..].
  sub t2, s3, s6              # remaining path nibbles
  mv t3, t1                   # cmp_limit = min(ext_count, remaining)
  bgeu t2, t1, .Liw_ext_lim_ok
  mv t3, t2
.Liw_ext_lim_ok:
  la t4, mw_nibble_buf
  add t5, s2, s6              # &path[consumed]
  li t6, 0                    # match counter
.Liw_ext_cmp:
  beq t6, t3, .Liw_ext_cmp_done
  add a0, t4, t6; lbu a1, 0(a0)
  add a0, t5, t6; lbu a2, 0(a0)
  bne a1, a2, .Liw_ext_cmp_done
  addi t6, t6, 1
  j .Liw_ext_cmp
.Liw_ext_cmp_done:
  # full match iff matched all ext nibbles AND ext fits in remaining path.
  bne t6, t1, .Liw_ext_split
  bgtu t1, t2, .Liw_ext_split # ext longer than remaining -> split
  # full extension match: push it and descend into its child (item 1).
  sub a0, s7, s0
  sd a0,  0(s4)
  sd s8,  8(s4)
  li a1, 1; sd a1, 16(s4)     # kind = 1 (extension)
  sd zero, 24(s4)
  addi s4, s4, 32
  addi s9, s9, 1
  add s6, s6, t1              # consume the ext nibbles
  mv a0, s7
  mv a1, s8
  li a2, 1
  la a3, mw_child_offset
  la a4, mw_child_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liw_parse_fail
  la t0, mw_child_length; ld t1, 0(t0)
  la t0, mw_child_offset; ld t2, 0(t0)
  add t3, s7, t2
  li t4, 32
  beq t1, t4, .Liw_ext_hash
  mv s7, t3
  mv s8, t1
  j .Liw_loop
.Liw_ext_hash:
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
  bnez a0, .Liw_miss
  la t0, mw_lookup_offset; ld t1, 0(t0); add s7, s0, t1
  la t0, mw_lookup_length; ld s8, 0(t0)
  j .Liw_loop
.Liw_ext_split:
  # t6 = match_len; the extension is the terminal (not pushed).
  li t5, 2                    # case 2 EXTENSION_SPLIT (t6 already = match_len)
  j .Liw_record
.Liw_leaf:
  mv a0, s7
  mv a1, s8
  li a2, 0
  la a3, mw_path_offset
  la a4, mw_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Liw_parse_fail
  la t0, mw_path_offset; ld t1, 0(t0); add a0, s7, t1
  la t0, mw_path_length; ld a1, 0(t0)
  la a2, mw_nibble_buf
  la a3, mw_nibble_count
  la a4, mw_is_leaf
  jal ra, hp_decode_nibbles
  bnez a0, .Liw_parse_fail
  la t0, mw_is_leaf; ld t1, 0(t0)
  li t2, 1
  bne t1, t2, .Liw_parse_fail # node kind said leaf; HP says extension
  la t0, mw_nibble_count; ld t1, 0(t0)    # t1 = leaf key nibble count
  sub t2, s3, s6              # remaining path nibbles
  mv t3, t1                   # cmp_limit = min(leaf_count, remaining)
  bgeu t2, t1, .Liw_leaf_lim_ok
  mv t3, t2
.Liw_leaf_lim_ok:
  la t4, mw_nibble_buf
  add t5, s2, s6              # &path[consumed]
  li t6, 0                    # match counter
.Liw_leaf_cmp:
  beq t6, t3, .Liw_leaf_cmp_done
  add a0, t4, t6; lbu a1, 0(a0)
  add a0, t5, t6; lbu a2, 0(a0)
  bne a1, a2, .Liw_leaf_cmp_done
  addi t6, t6, 1
  j .Liw_leaf_cmp
.Liw_leaf_cmp_done:
  # EXISTS iff matched all leaf nibbles AND leaf key length == remaining.
  bne t6, t1, .Liw_leaf_split
  bne t1, t2, .Liw_leaf_split
  li t5, 4                    # case 4 EXISTS (t6 already = match_len)
  j .Liw_record
.Liw_leaf_split:
  li t5, 1                    # case 1 LEAF_SPLIT (t6 already = match_len)
  j .Liw_record
.Liw_record:
  # t5 = case, t6 = match_len; terminal = (s7,s8); ancestors depth = s9.
  sd s9, 0(s5)               # depth
  sd s6, 8(s5)               # consumed
  sd t5, 16(s5)              # case
  sub t0, s7, s0; sd t0, 24(s5)  # terminal_offset
  sd s8, 32(s5)              # terminal_len
  sd t6, 40(s5)              # match_len
  li a0, 0
  j .Liw_ret
.Liw_empty:
  # case 3 EMPTY_TRIE: no ancestors, no terminal node.
  sd zero, 0(s5)             # depth = 0
  sd zero, 8(s5)             # consumed = 0
  sd t5, 16(s5)              # case = 3
  sd zero, 24(s5)            # terminal_offset = 0
  sd zero, 32(s5)            # terminal_len = 0
  sd zero, 40(s5)            # match_len = 0
  li a0, 0
  j .Liw_ret
.Liw_miss:
  li a0, 1
  j .Liw_ret
.Liw_parse_fail:
  li a0, 2
.Liw_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
