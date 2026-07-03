tx_gas_result_increments:
  bgtu a1, a0, .Ltgri_bad_remaining
  sub t0, a0, a1              # before_refund
  li t1, 5
  divu t2, t0, t1             # refund cap = before_refund / 5
  mv t3, a2                   # refund_counter
  bleu t3, t2, .Ltgri_refund_min_done
  mv t3, t2
.Ltgri_refund_min_done:
  sub t4, t0, t3              # after_refund
  mv t5, t0                   # block_inc = max(before_refund, floor)
  bleu a3, t5, .Ltgri_block_max_done
  mv t5, a3
.Ltgri_block_max_done:
  mv t6, t4                   # receipt_inc = max(after_refund, floor)
  bleu a3, t6, .Ltgri_receipt_max_done
  mv t6, a3
.Ltgri_receipt_max_done:
  li a0, 0
  mv a1, t5
  mv a2, t6
  mv a3, t0
  mv a4, t3
  ret
.Ltgri_bad_remaining:
  li a0, 1
  li a1, 0
  li a2, 0
  li a3, 0
  li a4, 0
  ret
