h_KECCAK256:
  la x14, evm_cur_stack_top
  ld x14, 0(x14)
  addi x14, x14, -64
  bgeu x14, x12, 137f
  li x5, 7
  la x6, evm_halt_flag
  sd x5, 0(x6)
  ret
137:
  ld x5, 40(x12)
  bnez x5, .exit_outofgas
  ld x5, 48(x12)
  bnez x5, .exit_outofgas
  ld x5, 56(x12)
  bnez x5, .exit_outofgas
  ld x15, 32(x12)
  beqz x15, .Lkeccak_range_ok
  ld x5, 8(x12)
  bnez x5, .exit_outofgas
  ld x5, 16(x12)
  bnez x5, .exit_outofgas
  ld x5, 24(x12)
  bnez x5, .exit_outofgas
  ld x14, 0(x12)
  add x5, x14, x15
  bltu x5, x14, .exit_outofgas
.Lkeccak_range_ok:
  ld x14, 0(x12)
  ld x15, 32(x12)
  addi x5, x15, 31
  bltu x5, x15, .exit_outofgas
  srli x5, x5, 5
  slli x6, x5, 2
  add x6, x6, x5
  add x6, x6, x5
  ld x5, 568(x20)
  bltu x5, x6, .exit_outofgas
  sub x5, x5, x6
  sd x5, 568(x20)
  beqz x15, .Lmemsize_keccak_done
  add x16, x14, x15
  addi x16, x16, 31
  li x18, -32
  and x16, x16, x18
  ld x17, 488(x20)
  bgeu x17, x16, .Lmemsize_keccak_done
  srli x18, x16, 5
  mulhu x6, x18, x18
  bnez x6, .exit_outofgas
  mul x6, x18, x18
  srli x6, x6, 9
  add x6, x6, x18
  add x6, x6, x18
  add x6, x6, x18
  srli x18, x17, 5
  mul x17, x18, x18
  srli x17, x17, 9
  add x17, x17, x18
  add x17, x17, x18
  add x17, x17, x18
  sub x6, x6, x17
  ld x18, 568(x20)
  bltu x18, x6, .exit_outofgas
  sub x18, x18, x6
  sd x18, 568(x20)
  ld x17, 488(x20)
  add x18, x13, x17
  add x6, x13, x16
.Lmemsize_keccak_zero:
  beq x18, x6, .Lmemsize_keccak_zero_done
  sd zero, 0(x18)
  addi x18, x18, 8
  j .Lmemsize_keccak_zero
.Lmemsize_keccak_zero_done:
  sd x16, 488(x20)
.Lmemsize_keccak_done:

  mv s10, x10
  ld t0, 0(x12)
  ld a1, 32(x12)
  addi x12, x12, 32
  add a0, x13, t0
  mv a2, x12
  mv s11, x12
  jal x1, zkvm_keccak256
  mv x10, s10
  mv x12, s11
  lbu x7, 0(x12)
  lbu x28, 31(x12)
  sb x28, 0(x12)
  sb x7, 31(x12)
  lbu x7, 1(x12)
  lbu x28, 30(x12)
  sb x28, 1(x12)
  sb x7, 30(x12)
  lbu x7, 2(x12)
  lbu x28, 29(x12)
  sb x28, 2(x12)
  sb x7, 29(x12)
  lbu x7, 3(x12)
  lbu x28, 28(x12)
  sb x28, 3(x12)
  sb x7, 28(x12)
  lbu x7, 4(x12)
  lbu x28, 27(x12)
  sb x28, 4(x12)
  sb x7, 27(x12)
  lbu x7, 5(x12)
  lbu x28, 26(x12)
  sb x28, 5(x12)
  sb x7, 26(x12)
  lbu x7, 6(x12)
  lbu x28, 25(x12)
  sb x28, 6(x12)
  sb x7, 25(x12)
  lbu x7, 7(x12)
  lbu x28, 24(x12)
  sb x28, 7(x12)
  sb x7, 24(x12)
  lbu x7, 8(x12)
  lbu x28, 23(x12)
  sb x28, 8(x12)
  sb x7, 23(x12)
  lbu x7, 9(x12)
  lbu x28, 22(x12)
  sb x28, 9(x12)
  sb x7, 22(x12)
  lbu x7, 10(x12)
  lbu x28, 21(x12)
  sb x28, 10(x12)
  sb x7, 21(x12)
  lbu x7, 11(x12)
  lbu x28, 20(x12)
  sb x28, 11(x12)
  sb x7, 20(x12)
  lbu x7, 12(x12)
  lbu x28, 19(x12)
  sb x28, 12(x12)
  sb x7, 19(x12)
  lbu x7, 13(x12)
  lbu x28, 18(x12)
  sb x28, 13(x12)
  sb x7, 18(x12)
  lbu x7, 14(x12)
  lbu x28, 17(x12)
  sb x28, 14(x12)
  sb x7, 17(x12)
  lbu x7, 15(x12)
  lbu x28, 16(x12)
  sb x28, 15(x12)
  sb x7, 16(x12)
  addi x10, x10, 1
  la x1, .dispatch_resume
  ret
