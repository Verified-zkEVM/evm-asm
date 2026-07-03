mset_memcpy:
  beqz a2, .Lmsetcpy_done
.Lmsetcpy_loop:
  lbu t0, 0(a1)
  sb t0, 0(a0)
  addi a0, a0, 1
  addi a1, a1, 1
  addi a2, a2, -1
  bnez a2, .Lmsetcpy_loop
.Lmsetcpy_done:
  ret
