exp_gas:
  li t0, 0                          # i = leading-zero byte count (scan from MSB)
.Lexp_lead:
  li t1, 32; beq t0, t1, .Lexp_zero # all 32 bytes zero -> exponent_bytes = 0
  add t2, a0, t0; lbu t2, 0(t2)
  bnez t2, .Lexp_found
  addi t0, t0, 1; j .Lexp_lead
.Lexp_found:
  li t1, 32; sub t1, t1, t0         # exponent_bytes = 32 - i
  li t2, 50; mul t1, t1, t2         # 50 * exponent_bytes
  addi a0, t1, 10                   # + EXP base
  ret
.Lexp_zero:
  li a0, 10
  ret
