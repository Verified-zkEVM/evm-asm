block_rlp_rebuilt_size:
  addi sp, sp, -96
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp); sd s10, 88(sp)
  mv s0, a0                   # payload
  mv s1, a1                   # header RLP length
  mv s2, a2                   # SSZ_BASE (reserved for future schema checks)
  addi a0, s0, 504; jal ra, bgv_u32le; mv s3, a0    # tx_off
  addi a0, s0, 508; jal ra, bgv_u32le; mv s4, a0    # withdrawals_off
  bltu s4, s3, .Lbrl_fail
  addi a0, s0, 528; jal ra, bgv_u32le; mv s5, a0    # block_access_list_off
  bltu s5, s4, .Lbrl_fail
  add s6, s0, s3              # tx section ptr
  sub s7, s4, s3              # tx section len
  li s8, 0                    # tx list payload length
  beqz s7, .Lbrl_tx_list_size
  mv a0, s6; jal ra, bgv_u32le; mv s9, a0           # first SSZ offset = 4*N
  li t0, 4; remu t1, s9, t0; bnez t1, .Lbrl_fail
  bltu s7, s9, .Lbrl_fail
  divu s10, s9, t0            # tx count
  li s2, 0                    # i
.Lbrl_tx_loop:
  bgeu s2, s10, .Lbrl_tx_list_size
  slli t3, s2, 2; add a0, s6, t3; jal ra, bgv_u32le; la t0, brl_item_start; sd a0, 0(t0)
  addi t5, s2, 1; bgeu t5, s10, .Lbrl_tx_last
  slli t6, t5, 2; add a0, s6, t6; jal ra, bgv_u32le; la t0, brl_item_end; sd a0, 0(t0); j .Lbrl_tx_have_end
.Lbrl_tx_last:
  la t0, brl_item_end; sd s7, 0(t0)
.Lbrl_tx_have_end:
  la t0, brl_item_start; ld t4, 0(t0); la t0, brl_item_end; ld t5, 0(t0)
  bltu t4, s9, .Lbrl_fail
  bltu t5, t4, .Lbrl_fail
  bltu s7, t5, .Lbrl_fail
  add t6, s6, t4; sub a1, t5, t4
  beqz a1, .Lbrl_tx_as_bytes
  lbu t0, 0(t6); li t1, 0xc0; bgeu t0, t1, .Lbrl_tx_as_legacy
.Lbrl_tx_as_bytes:
  mv a0, t6; jal ra, rlp_bytes_encoded_size
  add s8, s8, a0; j .Lbrl_tx_next
.Lbrl_tx_as_legacy:
  add s8, s8, a1
.Lbrl_tx_next:
  addi s2, s2, 1; j .Lbrl_tx_loop
.Lbrl_tx_list_size:
  mv a0, s8; jal ra, rlp_list_encoded_size; mv s8, a0
  add s6, s0, s4              # withdrawals section ptr
  sub s7, s5, s4              # withdrawals section len
  li t0, 44; remu t1, s7, t0; bnez t1, .Lbrl_fail
  divu s9, s7, t0             # withdrawal count
  li s10, 0                   # withdrawal list payload length
  li s2, 0
.Lbrl_wd_loop:
  bgeu s2, s9, .Lbrl_wd_list_size
  li t0, 44; mul t1, s2, t0; add a0, s6, t1
  la a1, brl_wd_buf; la a2, brl_wd_len; jal ra, ssz_withdrawal_to_rlp
  bnez a0, .Lbrl_fail
  la t0, brl_wd_len; ld t1, 0(t0); add s10, s10, t1
  addi s2, s2, 1; j .Lbrl_wd_loop
.Lbrl_wd_list_size:
  mv a0, s10; jal ra, rlp_list_encoded_size; mv s10, a0
  add t0, s1, s8              # header + txs
  addi t0, t0, 1              # empty ommers list = 0xc0
  add t0, t0, s10             # + withdrawals
  mv a0, t0; jal ra, rlp_list_encoded_size
  mv a1, a0; li a0, 0; j .Lbrl_ret
.Lbrl_fail:
  li a0, 1; li a1, 0
.Lbrl_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp); ld s10, 88(sp)
  addi sp, sp, 96
  ret
