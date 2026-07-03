keccak256_word_gas:
  addi t0, a0, 31; srli t0, t0, 5   # words
  li t1, 6; mul t0, t0, t1
  addi a0, t0, 30                   # + KECCAK256 base
  ret
