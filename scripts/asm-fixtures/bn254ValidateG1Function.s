bnc_validate_g1:
  addi sp, sp, -16
  sd ra, 0(sp); sd s0, 8(sp)
  mv s0, a0
  jal ra, bnf_lt_p
  beqz a0, .Lbnc_val_bad        # x >= p
  addi a0, s0, 32
  jal ra, bnf_lt_p
  beqz a0, .Lbnc_val_bad        # y >= p
  mv a0, s0
  jal ra, bnc_is_inf64
  beqz a0, .Lbnc_val_finite
  li a0, 1                      # (0,0) = infinity, valid
  j .Lbnc_val_ret
.Lbnc_val_finite:
  mv a0, s0
  jal ra, bnc_on_curve
  beqz a0, .Lbnc_val_bad
  li a0, 0
  j .Lbnc_val_ret
.Lbnc_val_bad:
  li a0, 2
.Lbnc_val_ret:
  ld ra, 0(sp); ld s0, 8(sp)
  addi sp, sp, 16
  ret
