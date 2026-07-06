bv_sum_withdrawals_to_address:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # target address ptr (20B)
  mv s1, a1                   # SSZ withdrawals base
  mv s2, a2                   # withdrawal count
  mv s3, a3                   # out u256 BE
  sd zero, 0(s3); sd zero, 8(s3); sd zero, 16(s3); sd zero, 24(s3)
  li s4, 0                    # i
.Lbsw_loop:
  beq s4, s2, .Lbsw_ok
  li t0, 44; mul t0, s4, t0; add t1, s1, t0   # entry ptr
  addi t2, t1, 16             # entry address @ +16
  mv t3, s0; li t4, 20
.Lbsw_addr_cmp:
  beqz t4, .Lbsw_match
  lbu t5, 0(t2); lbu t6, 0(t3); bne t5, t6, .Lbsw_next
  addi t2, t2, 1; addi t3, t3, 1; addi t4, t4, -1
  j .Lbsw_addr_cmp
.Lbsw_match:
  li t0, 44; mul t0, s4, t0; add t1, s1, t0   # re-derive entry ptr
  la t2, bsw_amount
  sd zero, 0(t2); sd zero, 8(t2); sd zero, 16(t2); sd zero, 24(t2)
  addi a0, t1, 36; li a1, 8; la a2, bsw_amount; addi a2, a2, 24
  jal ra, swr_rev_le_be       # amount_gwei LE@36 -> BE in low 8 bytes
  la a0, bsw_amount; li a1, 1000000000; la a2, bsw_wei
  jal ra, u256_mul_u64_be     # wei = amount_gwei * 1e9
  bnez a0, .Lbsw_overflow
  mv a0, s3; la a1, bsw_wei; mv a2, s3
  jal ra, u256_add_be         # acc += wei
  bnez a0, .Lbsw_overflow
.Lbsw_next:
  addi s4, s4, 1; j .Lbsw_loop
.Lbsw_ok:
  li a0, 0; j .Lbsw_ret
.Lbsw_overflow:
  li a0, 1
.Lbsw_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
