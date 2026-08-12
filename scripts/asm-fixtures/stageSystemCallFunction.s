stage_system_call:
  la t0, ssc_saved_ra; sd ra, 0(t0)
  la t0, ssc_saved_s0; sd s0, 0(t0)
  mv t1, a0; jal ra, account_read_record; mv a0, t1
  beqz a2, .Lssc_fail
  mv s0, a4                    # out payload ptr (used only pre-dispatch)
  li t0, 0; la t1, system_call_returndata_len; sd t0, 0(t1)
  li t0, 1; la t1, system_call_mode; sd t0, 0(t1)
  la t1, runtime_tx_auth_exec_fn; sd zero, 0(t1)
  la t0, rdg_halt_kind; sd zero, 0(t0)
  jal ra, stage_system_call_payload
  bnez a0, .Lssc_fail
  addi t1, s0, 8; la t0, runtime_dispatcher_input_ptr; sd t1, 0(t0)
  jal ra, runtime_dispatcher_call
  la t0, runtime_dispatcher_input_ptr; sd zero, 0(t0)
  li t0, 0; la t1, system_call_mode; sd t0, 0(t1)
  la a0, system_call_returndata
  la t0, system_call_returndata_len; ld a1, 0(t0)
  la t0, rdg_halt_kind; ld t1, 0(t0)
  beqz t1, .Lssc_ok
  li t0, 1; beq t1, t0, .Lssc_ok
  li t0, 5; beq t1, t0, .Lssc_ok
  li a2, 2
  j .Lssc_ret
.Lssc_ok:
  li a2, 0
  j .Lssc_ret
.Lssc_fail:
  li t0, 0; la t1, system_call_mode; sd t0, 0(t1)
  la a0, system_call_returndata; li a1, 0; li a2, 1
.Lssc_ret:
  la t0, ssc_saved_s0; ld s0, 0(t0)
  la t0, ssc_saved_ra; ld ra, 0(t0)
  ret
