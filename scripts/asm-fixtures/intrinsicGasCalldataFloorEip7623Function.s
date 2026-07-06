intrinsic_gas_calldata_floor_eip7623:
  # Count zeros and non-zeros in one pass.
  li t0, 0                    # zero_count
  li t1, 0                    # non_zero_count
  mv t2, a0                   # cursor
  mv t3, a1                   # remaining
.Ligcf_loop:
  beqz t3, .Ligcf_done
  lbu t4, 0(t2)
  bnez t4, .Ligcf_nz
  addi t0, t0, 1
  j .Ligcf_step
.Ligcf_nz:
  addi t1, t1, 1
.Ligcf_step:
  addi t2, t2, 1
  addi t3, t3, -1
  j .Ligcf_loop
.Ligcf_done:
  # tokens = zero + non_zero × token_per_nonzero
  mul t5, t1, a3              # non_zero × token_per_nz
  add t5, t5, t0              # tokens
  # floor = tokens × floor_gas_per_token + base_gas
  mul t6, t5, a2
  add t6, t6, a4
  sd t6, 0(a5)
  li a0, 0
  ret
