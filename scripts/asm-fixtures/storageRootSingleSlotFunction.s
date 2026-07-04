storage_root_single_slot:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                   # slot_key
  mv s1, a1                   # value ptr
  mv s2, a2                   # value len
  mv s3, a3                   # out root
  # The storage-trie leaf value is RLP(stored word), which the leaf node
  # then wraps again -- so RLP-encode the value FIRST (for a >=0x80 / multi-
  # byte word this adds the 0x80+len prefix; small words are unchanged).
  mv a0, s1; mv a1, s2; la a2, srss_rlpval; la a3, srss_rlpval_len
  jal ra, rlp_encode_bytes
  # trie key = keccak256(slot_key, 32) -> srss_key
  mv a0, s0; li a1, 32; la a2, srss_key
  jal ra, zkvm_keccak256
  # root = single_leaf_trie_root(srss_key, 32, RLP(value), len, out)
  la a0, srss_key; li a1, 32; la a2, srss_rlpval; la t0, srss_rlpval_len; ld a3, 0(t0); mv a4, s3
  jal ra, single_leaf_trie_root
  li a0, 0
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
