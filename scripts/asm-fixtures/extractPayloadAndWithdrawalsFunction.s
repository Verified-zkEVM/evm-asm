extract_payload_and_withdrawals:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # SSZ_BASE
  mv s1, a1                   # out payload ptr
  mv s2, a2                   # out withdrawals ptr
  mv s3, a3                   # out withdrawals count
  # NPR = SSZ_BASE + outer.offsets[0]
  mv a0, s0
  jal ra, spw_u32le
  add t2, s0, a0              # NPR addr
  # exec_payload = NPR + NPR.offsets[0]
  mv a0, t2
  jal ra, spw_u32le
  li t0, 44
  bne a0, t0, .Lspw_fail      # SszNewPayloadRequest fixed header before payload
  # a0 = NPR.offsets[0]; recompute NPR (t2 clobbered by call? spw_u32le uses only t0/t1)
  add s4, t2, a0              # s4 = exec_payload addr
  sd s4, 0(s1)                # out payload ptr
  # wd_off = u32 @ exec_payload+508
  addi a0, s4, 508
  jal ra, spw_u32le
  mv t4, a0                   # wd_off
  # bal_off = u32 @ exec_payload+528
  addi a0, s4, 528
  jal ra, spw_u32le
  mv t6, a0                   # bal_off; retain across the vh_off helper call
  # Require the VersionedHashes start to be at/after `44 + bal_off`.
  # Equivalently: NPR + vh_off >= exec_payload + bal_off.
  addi a0, t2, 4
  jal ra, spw_u32le
  addi t0, t6, 44
  bltu a0, t0, .Lspw_fail
  mv a0, t6
  # a0 = bal_off ; t4 = wd_off
  li t0, 540
  bltu t4, t0, .Lspw_fail     # withdrawals must start after the fixed payload part
  bltu a0, t4, .Lspw_fail     # block_access_list offset bounds withdrawals end
  add t5, s4, t4              # withdrawals_ptr = exec_payload + wd_off
  sd t5, 0(s2)
  sub t6, a0, t4              # withdrawals_len = bal_off - wd_off
  # count = withdrawals_len / 44 (repeated subtraction; count is small)
  li t0, 0                    # count
  li t1, 44
.Lspw_cnt:
  bltu t6, t1, .Lspw_cnt_done
  sub t6, t6, t1
  addi t0, t0, 1
  j .Lspw_cnt
.Lspw_cnt_done:
  bnez t6, .Lspw_fail         # fixed-size SSZ withdrawals must be N*44 bytes
  sd t0, 0(s3)                # out count
  li a0, 0
  j .Lspw_ret
.Lspw_fail:
  sd zero, 0(s1)
  sd zero, 0(s2)
  sd zero, 0(s3)
  li a0, 1
.Lspw_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
