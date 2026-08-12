multi_tx_sequential_gas_settle_step:
  addi sp, sp, -64
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6
  la t0, evm_env; sd s1, 568(t0)
  la t0, evm_state_gas_left; sd s2, 0(t0)
  la t0, evm_refund_acc; sd s3, 0(t0)
  la t0, evm_state_gas_used; sd s4, 0(t0)
  la t0, evm_state_gas_spilled; sd s5, 0(t0)
  la t0, rdg_halt_kind; sd s6, 0(t0)
  jal ra, dispatcher_tx_gas_settle
  sd a0, 0(s0); sd a1, 8(s0); sd a2, 16(s0)
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); addi sp, sp, 64
  ret
