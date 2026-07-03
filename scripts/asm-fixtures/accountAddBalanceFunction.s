account_add_balance:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp)
  mv s0, a0                   # account ptr
  mv s1, a1                   # account len
  mv s2, a2                   # delta32 ptr
  mv s3, a3                   # out ptr
  mv s4, a4                   # out_len ptr
  # read balance item (index 1).
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, aab_bal_off; la a4, aab_bal_len
  jal ra, rlp_list_nth_item
  bnez a0, .Laab_fail
  # zero the 32-byte balance buffer.
  la t0, aab_bal32
  sd zero, 0(t0); sd zero, 8(t0); sd zero, 16(t0); sd zero, 24(t0)
  la t1, aab_bal_len; ld t1, 0(t1)   # balance content length
  li t2, 32; bgtu t1, t2, .Laab_fail
  # src = account + bal_off; dst = aab_bal32 + (32 - bal_len) (right-align).
  la t2, aab_bal_off; ld t2, 0(t2); add t2, s0, t2
  la t3, aab_bal32; li t4, 32; sub t4, t4, t1; add t3, t3, t4
  mv t5, t1
.Laab_cp:
  beqz t5, .Laab_cp_done
  lbu t6, 0(t2); sb t6, 0(t3)
  addi t2, t2, 1; addi t3, t3, 1; addi t5, t5, -1
  j .Laab_cp
.Laab_cp_done:
  # big-endian add delta32 into aab_bal32: i = 31 .. 0, carry.
  la t0, aab_bal32                  # balance buf base
  li t2, 31                         # byte index
  li t3, 0                          # carry
.Laab_add:
  add t4, t0, t2                    # &bal[i]
  lbu t5, 0(t4)
  add t6, s2, t2; lbu t6, 0(t6)     # delta[i]
  add t5, t5, t6; add t5, t5, t3
  andi t6, t5, 0xff; sb t6, 0(t4)
  srli t3, t5, 8                    # new carry
  beqz t2, .Laab_add_done
  addi t2, t2, -1
  j .Laab_add
.Laab_add_done:
  # minimal length: first nonzero byte from index 0.
  la t0, aab_bal32; li t1, 0
.Laab_scan:
  li t2, 32; beq t1, t2, .Laab_scan_done
  add t3, t0, t1; lbu t3, 0(t3); bnez t3, .Laab_scan_done
  addi t1, t1, 1; j .Laab_scan
.Laab_scan_done:
  li t2, 32; sub t2, t2, t1         # minimal length
  la t3, aab_bal32; add t3, t3, t1  # minimal ptr
  # rlp_encode_bytes(minimal) -> aab_enc (the new balance item bytes).
  mv a0, t3; mv a1, t2
  la a2, aab_enc; la a3, aab_enc_len
  jal ra, rlp_encode_bytes
  # splice account item 1 with the new balance encoding.
  mv a0, s0; mv a1, s1; li a2, 1
  la a3, aab_enc; la t0, aab_enc_len; ld a4, 0(t0)
  mv a5, s3; mv a6, s4
  jal ra, mpt_splice_slot
  j .Laab_ret
.Laab_fail:
  li a0, 1
.Laab_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp)
  addi sp, sp, 64
  ret
