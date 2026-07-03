address_from_pubkey:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a1                   # output ptr (stash)
  # keccak256(pubkey, 64) → afp_digest
  li a1, 64
  la a2, afp_digest
  jal ra, zkvm_keccak256
  # Copy digest[12..32] (20 bytes) to output.
  la t0, afp_digest
  # 20 bytes = 8 + 8 + 4. Loads may be unaligned (offset 12).
  ld t1, 12(t0); sd t1,  0(s0)
  ld t1, 20(t0); sd t1,  8(s0)
  lwu t1, 28(t0); sw t1, 16(s0)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
