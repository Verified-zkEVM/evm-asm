process_block_start_system_transactions:
  la t0, pbsst_saved_ra; sd ra, 0(t0)
  la t0, current_block_access_index; sd zero, 0(t0)
  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)
  la t0, svf_witness; ld t1, 0(t0); la t2, bv_witness_state_ptr; sd t1, 0(t2)
  la t0, svf_witness_len; ld t1, 0(t0); la t2, bv_witness_state_len; sd t1, 0(t2)
  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)
  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)
  la a2, bsr_addr_4788
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  mv t0, a0; mv t1, a1; mv a0, a2; jal ra, account_read_record; mv a0, t0; mv a1, t1
  jal ra, code_at_header_state_root
  li t0, 1; beq a0, t0, .Lpbs_4788_skip
  li t0, 5; bne a0, t0, .Lpbs_4788_lookup_done
  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash
  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lpbs_4788_lookup_done
  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lpbs_4788_lookup_done
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lpbs_4788_lookup_done
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lpbs_4788_lookup_done
  j .Lpbs_4788_skip
.Lpbs_4788_lookup_done:
  bnez a0, .Lpbs_fail
  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lpbs_4788_skip
  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3
  la t0, pbsst_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, pbsst_code_len; sd t3, 0(t0)
  la t0, bv_exec_p; ld t1, 0(t0); addi t1, t1, -36
  la t0, ssc_calldata_ptr; sd t1, 0(t0); li t1, 32; la t0, ssc_calldata_len; sd t1, 0(t0)
  la a0, bsr_addr_4788
  la t0, pbsst_code_ptr; ld a1, 0(t0); la t0, pbsst_code_len; ld a2, 0(t0)
  la t0, bv_exec_p; ld a3, 0(t0); la a4, c1_staging
  jal ra, stage_system_call
  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)
  li t0, 1; beq a2, t0, .Lpbs_fail
  la t0, tx_account_writes_count; sd zero, 0(t0)
  jal ra, write_sets_incorporate_tx
  jal ra, read_sets_incorporate_tx
.Lpbs_4788_skip:
  la t0, svf_witness; ld a3, 0(t0); la t0, svf_witness_len; ld a4, 0(t0)
  la t0, svf_parent_rlp; ld a0, 0(t0); la t0, svf_parent_rlp_len; ld a1, 0(t0)
  la a2, bsr_addr_2935
  la t0, svf_codes_ptr; ld a5, 0(t0); la t0, svf_codes_len; ld a6, 0(t0)
  mv t0, a0; mv t1, a1; mv a0, a2; jal ra, account_read_record; mv a0, t0; mv a1, t1
  jal ra, code_at_header_state_root
  li t0, 1; beq a0, t0, .Lpbs_2935_skip
  li t0, 5; bne a0, t0, .Lpbs_2935_lookup_done
  la t0, cahsr_acct_struct; addi t0, t0, 72; la t1, chahsr_empty_code_hash
  ld t2, 0(t0); ld t3, 0(t1); bne t2, t3, .Lpbs_2935_lookup_done
  ld t2, 8(t0); ld t3, 8(t1); bne t2, t3, .Lpbs_2935_lookup_done
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lpbs_2935_lookup_done
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lpbs_2935_lookup_done
  j .Lpbs_2935_skip
.Lpbs_2935_lookup_done:
  bnez a0, .Lpbs_fail
  la t0, cahsr_code_length; ld t0, 0(t0); beqz t0, .Lpbs_2935_skip
  la t0, svf_codes_ptr; ld t1, 0(t0); la t2, cahsr_code_offset; ld t3, 0(t2); add t4, t1, t3
  la t0, pbsst_code_ptr; sd t4, 0(t0); la t2, cahsr_code_length; ld t3, 0(t2); la t0, pbsst_code_len; sd t3, 0(t0)
  la t0, bv_exec_p; ld t1, 0(t0)
  la t0, ssc_calldata_ptr; sd t1, 0(t0); li t1, 32; la t0, ssc_calldata_len; sd t1, 0(t0)
  la a0, bsr_addr_2935
  la t0, pbsst_code_ptr; ld a1, 0(t0); la t0, pbsst_code_len; ld a2, 0(t0)
  la t0, bv_exec_p; ld a3, 0(t0); la a4, c1_staging
  jal ra, stage_system_call
  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)
  li t0, 1; beq a2, t0, .Lpbs_fail
  la t0, tx_account_writes_count; sd zero, 0(t0)
  jal ra, write_sets_incorporate_tx
  jal ra, read_sets_incorporate_tx
.Lpbs_2935_skip:
  la t0, evm_oldest_ancestor_offset; ld t1, 0(t0); bnez t1, .Lpbs_ok
  li t1, 1; sd t1, 0(t0)
.Lpbs_ok:
  li a0, 0
  j .Lpbs_ret
.Lpbs_fail:
  la t0, ssc_calldata_ptr; sd zero, 0(t0); la t0, ssc_calldata_len; sd zero, 0(t0)
  li a0, 1
.Lpbs_ret:
  la t0, pbsst_saved_ra; ld ra, 0(t0)
  ret
