mpt_one_leaf_root_indexed:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # value ptr
  mv s1, a1                   # value len
  mv s2, a2                   # output root ptr
  # Build path = [8, 0] (rlp(0)=0x80 -> nibbles [8,0])
  la t0, mtoli_nibbles
  li t1, 8; sb t1, 0(t0)
  li t1, 0; sb t1, 1(t0)
  # ---- Encode leaf node ----
  la a0, mtoli_nibbles
  li a1, 2
  mv a2, s0; mv a3, s1
  la a4, mtoli_leaf_buf
  la a5, mtoli_leaf_len
  jal ra, mpt_leaf_node_encode_from_nibbles
  # ---- keccak256 the leaf ----
  la a0, mtoli_leaf_buf
  la t0, mtoli_leaf_len; ld a1, 0(t0)
  mv a2, s2
  jal ra, zkvm_keccak256
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
