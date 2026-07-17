eip8037_prior_state_used_exact:
  # a0 = prior tx count (0-based current tx index), a1 = out ptr.
  # Returns a0=0 when the execution-derived prior-state sum is exact, else 1.
  sd zero, 0(a1)
  beqz a0, .Lepse_ok
  la t0, bsg_exact_state_ok; ld t0, 0(t0); beqz t0, .Lepse_fail
  la t0, bvgr_runtime_count; ld t0, 0(t0); bltu t0, a0, .Lepse_fail
  li t0, 16; bgtu a0, t0, .Lepse_fail
  mv t0, a0                   # prior count
  li t1, 0                    # i
  li t2, 0                    # accumulated state gas
.Lepse_loop:
  beq t1, t0, .Lepse_store
  slli t3, t1, 3
  la t4, bvgr_tx_state_gas; add t4, t4, t3; ld t5, 0(t4)
  add t6, t2, t5; bltu t6, t2, .Lepse_fail; mv t2, t6
  la t4, bv_tx_status_arr; add t4, t4, t3; ld t5, 0(t4); beqz t5, .Lepse_next
  la t4, bvgr_tx_exec_state_gas; add t4, t4, t3; ld t5, 0(t4)
  add t6, t2, t5; bltu t6, t2, .Lepse_fail; mv t2, t6
.Lepse_next:
  addi t1, t1, 1; j .Lepse_loop
.Lepse_store:
  sd t2, 0(a1)
.Lepse_ok:
  li a0, 0; ret
.Lepse_fail:
  li a0, 1; ret
