copy_word_gas:
  addi t0, a0, 31; srli t0, t0, 5   # words
  li t1, 3; mul a0, t0, t1
  ret
