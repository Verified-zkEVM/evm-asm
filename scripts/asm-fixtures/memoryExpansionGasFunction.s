memory_expansion_gas:
  bgeu a0, a1, .Lmeg_zero        # new <= old -> no expansion
  addi t0, a0, 31; srli t0, t0, 5   # t0 = words_old = (old+31)/32
  addi t1, a1, 31; srli t1, t1, 5   # t1 = words_new = (new+31)/32
  li t2, 3
  mul t3, t0, t2                 # words_old * 3
  mul t4, t0, t0; srli t4, t4, 9 # words_old^2 / 512
  add t3, t3, t4                 # cost_old
  mul t5, t1, t2                 # words_new * 3
  mul t6, t1, t1; srli t6, t6, 9 # words_new^2 / 512
  add t5, t5, t6                 # cost_new
  sub a0, t5, t3                 # expansion = cost_new - cost_old
  ret
.Lmeg_zero:
  li a0, 0
  ret
