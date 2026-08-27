eip7778_remaining_block_gas_check:
  addi sp, sp, -16
  sd s0, 0(sp)
  mv s0, a4                   # a4 reserved for callers' intrinsic-state array
  mv t0, a0                   # block_gas_limit
  mv t1, a1                   # tx_gas ptr
  mv t2, a2                   # block_gas_used_in_tx ptr
  mv t3, a3                   # count
  li t4, 0                    # i
  li t5, 0                    # block_gas_used
.Le7778_loop:
  beq t4, t3, .Le7778_ok
  bltu t0, t5, .Le7778_tx_fail
  slli t6, t4, 3
  add a4, t1, t6
  ld a5, 0(a4)                # tx.gas
  li a7, 16777216             # TX_MAX_GAS_LIMIT (2^24)
  bleu a5, a7, .Le7778_cap_done
  mv a5, a7                   # worst_regular = min(TX_MAX_GAS_LIMIT, tx.gas)
.Le7778_cap_done:
  sub a6, t0, t5              # gas_available
  bgtu a5, a6, .Le7778_tx_fail
  add a4, t2, t6
  ld a5, 0(a4)                # exact block_gas_used_in_tx
  add a6, t5, a5
  bltu a6, t5, .Le7778_overflow
  mv t5, a6
  addi t4, t4, 1
  j .Le7778_loop
.Le7778_tx_fail:
  li a0, 1
  addi a1, t4, 1
  mv a2, t5
  j .Le7778_ret
.Le7778_overflow:
  li a0, 2
  addi a1, t4, 1
  mv a2, t5
  j .Le7778_ret
.Le7778_ok:
  li a0, 0
  li a1, 0
  mv a2, t5
.Le7778_ret:
  ld s0, 0(sp)
  addi sp, sp, 16
  ret
