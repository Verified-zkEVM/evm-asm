calldata_byte_counts:
  # Pure-leaf, but we read into t-regs and update in-place; no
  # callee-saved usage needed.
  li t0, 0                    # zero_count
  li t1, 0                    # non_zero_count
  mv t2, a0                   # cursor
  mv t3, a1                   # remaining bytes
.Lcbc_loop:
  beqz t3, .Lcbc_done
  lbu t4, 0(t2)
  bnez t4, .Lcbc_nz
  addi t0, t0, 1
  j .Lcbc_step
.Lcbc_nz:
  addi t1, t1, 1
.Lcbc_step:
  addi t2, t2, 1
  addi t3, t3, -1
  j .Lcbc_loop
.Lcbc_done:
  sd t0, 0(a2)
  sd t1, 0(a3)
  li a0, 0
  ret
