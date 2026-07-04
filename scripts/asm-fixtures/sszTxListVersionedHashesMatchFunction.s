ssz_tx_list_versioned_hashes_match:
  addi sp, sp, -112
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp); sd s11, 96(sp)
  mv s0, a0                   # execution_payload ptr
  mv s1, a1                   # versioned_hashes ptr
  mv s2, a2                   # versioned_hashes byte length
  andi t0, s2, 31
  bnez t0, .Ltvhm_bad_ssz
  srli s3, s2, 5              # expected hash count
  li s4, 0                    # consumed hash count
  addi a0, s0, 504; jal ra, bgv_u32le       # transactions_offset
  mv s5, a0
  addi a0, s0, 508; jal ra, bgv_u32le       # withdrawals_offset
  add t0, s0, a0
  add s6, s0, s5              # tx list ptr
  bltu t0, s6, .Ltvhm_bad_ssz
  sub s7, t0, s6              # tx list len
  beqz s7, .Ltvhm_after_txs
  li t0, 4
  bltu s7, t0, .Ltvhm_bad_ssz
  mv a0, s6; jal ra, bgv_u32le
  andi t0, a0, 3
  beqz a0, .Ltvhm_bad_ssz
  bgtu a0, s7, .Ltvhm_bad_ssz
  srli s8, a0, 2              # tx_count = first offset / 4
  li s9, 0                    # tx index
.Ltvhm_tx_loop:
  beq s9, s8, .Ltvhm_after_txs
  slli t0, s9, 2; add t1, s6, t0; mv a0, t1; jal ra, bgv_u32le
  mv s10, a0                  # item_off
  slli t0, s8, 2
  bltu s10, t0, .Ltvhm_bad_ssz
  addi t0, s9, 1
  beq t0, s8, .Ltvhm_last_tx
  slli t1, t0, 2; add t1, s6, t1; mv a0, t1; jal ra, bgv_u32le
  j .Ltvhm_have_tx_end
.Ltvhm_last_tx:
  mv a0, s7
.Ltvhm_have_tx_end:
  bltu a0, s10, .Ltvhm_bad_ssz
  sub s11, a0, s10            # tx len
  add t0, s6, s10             # tx ptr
  mv a0, t0; mv a1, s11; la a2, tvhm_tx_type; la a3, tvhm_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Ltvhm_tx_fail
  la t0, tvhm_tx_type; ld t1, 0(t0)
  li t2, 3
  bne t1, t2, .Ltvhm_next_tx
  la t0, tvhm_inner_off; ld t1, 0(t0)
  bgtu t1, s11, .Ltvhm_tx_fail
  add t0, s6, s10; add s10, t0, t1      # inner ptr
  sub s11, s11, t1                      # inner len
  mv a0, s10; mv a1, s11; la a2, tvhm_struct
  jal ra, tx_eip4844_decode
  bnez a0, .Ltvhm_tx_fail
  la t0, tvhm_struct
  lwu t1, 168(t0); lwu t2, 172(t0)
  add s10, s10, t1             # blob hash list ptr
  mv s11, t2                   # blob hash list len
  mv a0, s10; mv a1, s11; la a2, tvhm_blob_count
  jal ra, rlp_list_count_items
  bnez a0, .Ltvhm_bad_blob_item
  la t0, tvhm_blob_count; ld t0, 0(t0)
  li t1, 0
.Ltvhm_blob_loop:
  beq t1, t0, .Ltvhm_next_tx
  bgeu s4, s3, .Ltvhm_mismatch
  mv a0, s10; mv a1, s11; mv a2, t1; la a3, tvhm_hash_off; la a4, tvhm_hash_len
  la t2, tvhm_blob_index; sd t1, 0(t2)
  jal ra, rlp_list_nth_item
  bnez a0, .Ltvhm_bad_blob_item
  la t2, tvhm_blob_count; ld t0, 0(t2); la t2, tvhm_blob_index; ld t1, 0(t2)
  la t2, tvhm_hash_len; ld t3, 0(t2)
  li t4, 32
  bne t3, t4, .Ltvhm_bad_blob_item
  la t2, tvhm_hash_off; ld t3, 0(t2)
  add t3, s10, t3              # actual hash ptr
  slli t4, s4, 5
  add t4, s1, t4               # expected hash ptr
  li t5, 0
.Ltvhm_hash_cmp:
  li t6, 32
  beq t5, t6, .Ltvhm_hash_equal
  add t6, t3, t5; lbu t6, 0(t6)
  add a5, t4, t5; lbu a5, 0(a5)
  bne t6, a5, .Ltvhm_mismatch
  addi t5, t5, 1
  j .Ltvhm_hash_cmp
.Ltvhm_hash_equal:
  addi s4, s4, 1
  addi t1, t1, 1
  j .Ltvhm_blob_loop
.Ltvhm_next_tx:
  addi s9, s9, 1
  j .Ltvhm_tx_loop
.Ltvhm_after_txs:
  bne s4, s3, .Ltvhm_mismatch
  li a0, 0
  j .Ltvhm_ret
.Ltvhm_bad_ssz:
  li a0, 1; j .Ltvhm_ret
.Ltvhm_tx_fail:
  li a0, 2; j .Ltvhm_ret
.Ltvhm_bad_blob_item:
  li a0, 3; j .Ltvhm_ret
.Ltvhm_mismatch:
  li a0, 4; j .Ltvhm_ret
.Ltvhm_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp); ld s11, 96(sp)
  addi sp, sp, 112
  ret
