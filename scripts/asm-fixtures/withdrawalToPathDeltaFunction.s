withdrawal_to_path_delta:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a2                   # out path ptr
  mv s1, a3                   # out delta ptr
  # decode the withdrawal RLP into wtpd_struct (a0/a1 already set).
  la a2, wtpd_struct
  jal ra, withdrawal_decode
  bnez a0, .Lwtpd_fail
  # keccak256(address @ struct+16, 20 bytes) -> wtpd_hash.
  la a0, wtpd_struct; addi a0, a0, 16
  li a1, 20
  la a2, wtpd_hash
  jal ra, zkvm_keccak256
  # path = bytes_to_nibbles(wtpd_hash, 32) -> out path (64 nibbles).
  la a0, wtpd_hash; li a1, 32; mv a2, s0
  jal ra, bytes_to_nibbles
  # delta = amount (Gwei, struct+40) zero-extended to u256 BE...
  la t0, wtpd_struct; ld a0, 40(t0)
  mv a1, s1
  jal ra, u256_from_u64_be
  # ... times 1e9 (Gwei -> wei), in place.
  mv a0, s1; li a1, 1000000000; mv a2, s1
  jal ra, u256_mul_u64_be
  bnez a0, .Lwtpd_fail
  li a0, 0
  j .Lwtpd_ret
.Lwtpd_fail:
  li a0, 1
.Lwtpd_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
