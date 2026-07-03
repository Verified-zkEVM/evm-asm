init_code_cost:
  addi t0, a0, 31             # len + 31
  srli t0, t0, 5              # / 32 → ceil(len/32)
  mul t0, t0, a1              # × gas_per_word
  sd t0, 0(a2)
  li a0, 0
  ret
