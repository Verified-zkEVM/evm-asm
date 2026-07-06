tx_pubkey_public_key_matches:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # chain_id
  mv s3, a3                   # supplied public_key (0x04 || x || y)
  mv s4, a4                   # recovered pubkey out (64 bytes)
  mv s5, a5                   # recover scratch (>= 304 bytes)
  # 1. SEC1 uncompressed prefix must be 0x04 (cheap; before recovery).
  lbu t0, 0(s3)
  li t1, 4
  bne t0, t1, .Ltpm_bad_prefix
  # 2. Recover the canonical public key from the transaction signature.
  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s4; mv a4, s5
  jal ra, tx_pubkey_recover_raw
  bnez a0, .Ltpm_ret          # propagate material/stage/recovery failure
  # 3. Byte-compare supplied[1..65] against recovered x||y (64 bytes).
  addi t0, s3, 1              # supplied coordinate bytes
  mv t1, s4                   # recovered coordinate bytes
  li t2, 64
.Ltpm_cmp:
  lbu t3, 0(t0); lbu t4, 0(t1)
  bne t3, t4, .Ltpm_mismatch
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1
  bnez t2, .Ltpm_cmp
  li a0, 0
  j .Ltpm_ret
.Ltpm_mismatch:
  li a0, 1
  j .Ltpm_ret
.Ltpm_bad_prefix:
  li a0, 2
.Ltpm_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
