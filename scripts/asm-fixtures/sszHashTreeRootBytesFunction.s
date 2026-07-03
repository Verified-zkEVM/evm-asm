ssz_hash_tree_root_bytes:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  # s0 = src; s1 = L; s2 = limit_log2; s3 = out ptr
  mv s0, a0
  mv s1, a1
  mv s2, a2
  mv s3, a3
  # Step 1: pack(src, L) -> ssz_hb_chunks. Returns chunk count in a0.
  mv a0, s0
  mv a1, s1
  la a2, ssz_hb_chunks
  jal ra, ssz_pack_bytes
  mv s4, a0                  # s4 = chunks count
  # Step 2: merkleize(ssz_hb_chunks, s4, s2, ssz_hb_partial)
  la a0, ssz_hb_chunks
  mv a1, s4
  mv a2, s2
  la a3, ssz_hb_partial
  jal ra, ssz_merkleize
  # Step 3: write length chunk (u256 LE of L) at ssz_hb_mix + 32..64
  # Copy partial root into ssz_hb_mix[0..32]
  la t0, ssz_hb_partial
  la t1, ssz_hb_mix
  ld t2,  0(t0); sd t2,  0(t1)
  ld t2,  8(t0); sd t2,  8(t1)
  ld t2, 16(t0); sd t2, 16(t1)
  ld t2, 24(t0); sd t2, 24(t1)
  # Length chunk at ssz_hb_mix + 32..64: u64 LE of L, then 24 zero bytes.
  sd s1, 32(t1)               # low 8 bytes = L (LE)
  sd zero, 40(t1)
  sd zero, 48(t1)
  sd zero, 56(t1)
  # Step 4: sha256(ssz_hb_mix, 64) -> caller's out ptr (s3)
  la a0, ssz_hb_mix
  li a1, 64
  mv a2, s3
  jal ra, zkvm_sha256
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 64
  ret
