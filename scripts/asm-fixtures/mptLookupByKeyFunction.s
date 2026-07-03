mpt_lookup_by_key:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a2                   # s0 = root_hash ptr
  mv s1, a3                   # s1 = witness ptr
  mv s2, a4                   # s2 = witness_len
  mv s3, a5                   # s3 = value out
  mv s4, a6                   # s4 = value_len out
  # Step 1: keccak(key) -> mlk_keccak_buf.
  la a2, mlk_keccak_buf
  jal ra, zkvm_keccak256
  # Step 2: bytes_to_nibbles(mlk_keccak_buf, 32, mlk_nibble_buf).
  la a0, mlk_keccak_buf
  li a1, 32
  la a2, mlk_nibble_buf
  jal ra, bytes_to_nibbles
  # Step 3: mpt_walk(root, witness, witness_len, path, 64, val_out, val_len).
  mv a0, s0
  mv a1, s1
  mv a2, s2
  la a3, mlk_nibble_buf
  li a4, 64
  mv a5, s3
  mv a6, s4
  jal ra, mpt_walk
  # a0 already holds mpt_walk's status.
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 64
  ret
