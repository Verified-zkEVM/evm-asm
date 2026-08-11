assemble_execution_requests:
  li x5, 20
  sw x5, 0(x16)
  add x5, x5, x11
  sw x5, 4(x16)
  add x5, x5, x13
  sw x5, 8(x16)
  add x5, x5, x15
  sw x5, 12(x16)
  la x7, aer_bd_len
  ld x28, 0(x7)
  add x5, x5, x28
  sw x5, 16(x16)
  addi x6, x16, 20
  mv x7, x10
  mv x28, x11
.Laer_dcopy:
  beq x28, x0, .Laer_dd
  lbu x29, 0(x7)
  sb x29, 0(x6)
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .Laer_dcopy
.Laer_dd:
  mv x7, x12
  mv x28, x13
.Laer_wcopy:
  beq x28, x0, .Laer_wd
  lbu x29, 0(x7)
  sb x29, 0(x6)
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .Laer_wcopy
.Laer_wd:
  mv x7, x14
  mv x28, x15
.Laer_ccopy:
  beq x28, x0, .Laer_cd
  lbu x29, 0(x7)
  sb x29, 0(x6)
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .Laer_ccopy
.Laer_cd:
  la x7, aer_bd_ptr
  ld x7, 0(x7)
  la x28, aer_bd_len
  ld x28, 0(x28)
.Laer_bd_copy:
  beq x28, x0, .Laer_bd_done
  lbu x29, 0(x7)
  sb x29, 0(x6)
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .Laer_bd_copy
.Laer_bd_done:
  la x7, aer_be_ptr
  ld x7, 0(x7)
  la x28, aer_be_len
  ld x28, 0(x28)
.Laer_be_copy:
  beq x28, x0, .Laer_be_done
  lbu x29, 0(x7)
  sb x29, 0(x6)
  addi x6, x6, 1
  addi x7, x7, 1
  addi x28, x28, -1
  jal x0, .Laer_be_copy
.Laer_be_done:
  li x10, 20
  add x10, x10, x11
  add x10, x10, x13
  add x10, x10, x15
  la x7, aer_bd_len
  ld x28, 0(x7)
  add x10, x10, x28
  la x7, aer_be_len
  ld x28, 0(x7)
  add x10, x10, x28
  jalr x0, 0(x1)
