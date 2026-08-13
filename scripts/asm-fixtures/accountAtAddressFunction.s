account_at_address:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp)
  mv s0, a5                   # output struct ptr
  # Step 1: mpt_lookup_by_key.
  la a5, aa_value_scratch
  la a6, aa_value_len
  jal ra, mpt_lookup_by_key
  mv s1, a0                   # save lookup status
  beqz a0, .Laa_lookup_ok
  # Not found / parse / unresolved: zero the output struct.
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)
  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)
  sd zero, 96(s0)
  # STATUS_VOCAB: walk→account — remap Walk.unresolved(3) → Account.unresolved(4)
  li t0, 3
  bne s1, t0, .Laa_propagate
  li a0, 4
  j .Laa_ret
.Laa_propagate:
  mv a0, s1                   # absent=1 / parse=2 pass through
  j .Laa_ret
.Laa_lookup_ok:
  la a0, aa_value_scratch
  la t0, aa_value_len; ld a1, 0(t0)
  mv a2, s0                   # nonce at struct + 0
  addi a3, s0, 8              # balance at struct + 8
  addi a4, s0, 40             # storage_root at struct + 40
  addi a5, s0, 72             # code_hash at struct + 72
  jal ra, account_decode
  beqz a0, .Laa_done
  # account_decode failed: zero struct, return 3.
  sd zero,  0(s0); sd zero,  8(s0); sd zero, 16(s0); sd zero, 24(s0)
  sd zero, 32(s0); sd zero, 40(s0); sd zero, 48(s0); sd zero, 56(s0)
  sd zero, 64(s0); sd zero, 72(s0); sd zero, 80(s0); sd zero, 88(s0)
  sd zero, 96(s0)
  li a0, 3
  j .Laa_ret
.Laa_done:
  li a0, 0
.Laa_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
