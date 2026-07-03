address_compute_create2:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # sender ptr
  mv s1, a1                   # salt ptr
  mv s4, a4                   # output ptr (stash)
  # Step 1: inner = keccak256(init_code).
  # init_code ptr/len already in (a2, a3); rotate into (a0, a1).
  mv a0, a2
  mv a1, a3
  la a2, ac2_inner_digest
  jal ra, zkvm_keccak256
  # Step 2: build preimage.
  la s2, ac2_preimage
  li t0, 0xff
  sb t0, 0(s2)
  # Copy sender 20 B → preimage[1..21] (8 + 8 + 4).
  ld t0,  0(s0); sd t0,  1(s2)
  ld t0,  8(s0); sd t0,  9(s2)
  lwu t0, 16(s0); sw t0, 17(s2)
  # Copy salt 32 B → preimage[21..53] (8 × 4).
  ld t0,  0(s1); sd t0, 21(s2)
  ld t0,  8(s1); sd t0, 29(s2)
  ld t0, 16(s1); sd t0, 37(s2)
  ld t0, 24(s1); sd t0, 45(s2)
  # Copy inner digest 32 B → preimage[53..85].
  la t1, ac2_inner_digest
  ld t0,  0(t1); sd t0, 53(s2)
  ld t0,  8(t1); sd t0, 61(s2)
  ld t0, 16(t1); sd t0, 69(s2)
  ld t0, 24(t1); sd t0, 77(s2)
  # Step 3: outer = keccak256(preimage, 85).
  mv a0, s2
  li a1, 85
  la a2, ac2_outer_digest
  jal ra, zkvm_keccak256
  # Step 4: copy outer[12..32] (20 B) → out.
  la t0, ac2_outer_digest
  ld t1, 12(t0); sd t1,  0(s4)
  ld t1, 20(t0); sd t1,  8(s4)
  lwu t1, 28(t0); sw t1, 16(s4)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
