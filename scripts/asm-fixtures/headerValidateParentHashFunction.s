header_validate_parent_hash:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a2                   # parent_rlp ptr (stash)
  mv s1, a3                   # parent_rlp_len (stash)
  # Step 1: extract this header's parent_hash (field 0).
  la a2, hvph_claimed
  jal ra, headers_parent_hash
  beqz a0, .Lhvph_hash
  li a0, 1
  j .Lhvph_ret
.Lhvph_hash:
  # Step 2: keccak256(parent_rlp) → hvph_computed.
  mv a0, s0
  mv a1, s1
  la a2, hvph_computed
  jal ra, zkvm_keccak256
  # zkvm_keccak256 always returns 0 (ZKVM_EOK).
  # Step 3: byte-by-byte compare (32 bytes via 4 × dword).
  la t0, hvph_claimed
  la t1, hvph_computed
  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lhvph_diff
  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lhvph_diff
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lhvph_diff
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lhvph_diff
  li a0, 0
  j .Lhvph_ret
.Lhvph_diff:
  li a0, 2
.Lhvph_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
