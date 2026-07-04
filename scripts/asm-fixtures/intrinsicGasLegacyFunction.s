intrinsic_gas_legacy:
  li t0, 21000               # base
  beqz a2, .Ligl_skip_creation
  li t1, 32000
  add t0, t0, t1
.Ligl_skip_creation:
  mv t2, a0                  # data cursor
  add t3, a0, a1             # data end
.Ligl_loop:
  bgeu t2, t3, .Ligl_done
  lbu t4, 0(t2)
  beqz t4, .Ligl_zero
  addi t0, t0, 16
  j .Ligl_step
.Ligl_zero:
  addi t0, t0, 4
.Ligl_step:
  addi t2, t2, 1
  j .Ligl_loop
.Ligl_done:
  mv a0, t0
  ret
