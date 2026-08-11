block_hash_and_extract_number:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1                # header
  mv s2, a3                            # number out ptr (stash)
  # 1. block_hash -> a2 (already set by caller)
  jal ra, block_hash_from_header
  # 2. number -> via rlp_field_to_u64_strict(header, len, 8, &out)
  mv a0, s0; mv a1, s1; li a2, 8
  mv a3, s2
  jal ra, rlp_field_to_u64_strict
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
