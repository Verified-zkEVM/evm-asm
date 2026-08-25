bal_serializer_rebuild_hash:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0; mv s1, a1
  jal ra, bal_builder_incorporate_touched_accounts
  la a0, bal_builder_storage_changes
  la t0, bal_builder_storage_change_count; ld a1, 0(t0)
  li a2, 96; li a3, 0x0818a0209400; li a4, 3; li a5, 47522
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  bnez a0, .Lbsrh_ret
  li a0, 0xa1908780  # STORAGE_READS_AREA
  la t0, storage_reads_count; ld a1, 0(t0)
  li a2, 64; li a3, 0x2020; li a4, 1; li a5, 66666
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  bnez a0, .Lbsrh_ret
  la a0, bal_builder_balance_changes
  la t0, bal_builder_balance_count; ld a1, 0(t0)
  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, 105000
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  bnez a0, .Lbsrh_ret
  la a0, bal_builder_nonce_changes
  la t0, bal_builder_nonce_count; ld a1, 0(t0)
  li a2, 40; li a3, 0x08189400; li a4, 2; li a5, 35000
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  bnez a0, .Lbsrh_ret
  la a0, bal_builder_code_changes
  la t0, bal_builder_code_count; ld a1, 0(t0)
  li a2, 64; li a3, 0x08189400; li a4, 2; li a5, 13125
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  bnez a0, .Lbsrh_ret
  la a0, bal_builder_accounts
  la t0, bal_builder_account_count; ld a1, 0(t0)
  li a2, 24; li a3, 0x9400; li a4, 1; li a5, 140000
  jal ra, bal_canonical_sort
  la t0, bal_serializer_sort_status; sd a0, 0(t0)
  beqz a0, .Lbsrh_sorted
  j .Lbsrh_ret
.Lbsrh_sorted:
  la a0, bal_serializer_rebuilt_ctx; jal ra, keccak_init
  la a0, bal_serializer_rebuilt_ctx; mv a1, s0; jal ra, bal_serializer_emit_outer
  la a0, bal_serializer_rebuilt_ctx; mv a1, s1; jal ra, keccak_final
  li a0, 0
.Lbsrh_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
