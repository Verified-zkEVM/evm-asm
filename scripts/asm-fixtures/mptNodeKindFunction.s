mpt_node_kind:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a0                  # node ptr
  mv s1, a1                  # node_len
  # #11347: count the items. execution-specs `decodeNodeItemAux` rejects a node
  # list whose length is not 17; the old code probed item 2 and treated "present"
  # as "17-item branch", which also accepts 3..16 and 18+.
  la a2, mnk_item_count
  jal ra, rlp_list_count_items
  bnez a0, .Lmnk_fail        # count failed ⇒ parse fail
  la t0, mnk_item_count
  ld t1, 0(t0)
  li t2, 17
  beq t1, t2, .Lmnk_branch   # exactly 17 ⇒ branch
  li t2, 2
  bne t1, t2, .Lmnk_fail     # neither 2 nor 17 ⇒ malformed
  # 2-item list ⇒ leaf or extension. Get item 0 to read path's first byte.
  mv a0, s0
  mv a1, s1
  li a2, 0
  la a3, mnk_path_offset
  la a4, mnk_path_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lmnk_fail        # item 0 missing ⇒ parse fail
  la t0, mnk_path_offset
  ld t1, 0(t0)               # path content offset
  la t0, mnk_path_length
  ld t2, 0(t0)               # path content length
  beqz t2, .Lmnk_fail        # empty path ⇒ malformed HP
  add t3, s0, t1             # path byte ptr
  lbu t4, 0(t3)
  srli t4, t4, 4             # high nibble
  li t5, 2
  bltu t4, t5, .Lmnk_extension  # 0,1 → extension
  li t5, 4
  bltu t4, t5, .Lmnk_leaf       # 2,3 → leaf
  j .Lmnk_fail                   # ≥ 4 → invalid HP
.Lmnk_branch:
  li a0, 0
  j .Lmnk_ret
.Lmnk_extension:
  li a0, 1
  j .Lmnk_ret
.Lmnk_leaf:
  li a0, 2
  j .Lmnk_ret
.Lmnk_fail:
  li a0, 3
.Lmnk_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
