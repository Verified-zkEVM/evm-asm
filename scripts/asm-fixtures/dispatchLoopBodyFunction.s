.dispatch_loop_body:
  lbu x5, 0(x10)
  slli x5, x5, 3
  la x6, opcode_gas_costs
  add x6, x6, x5
  ld x6, 0(x6)
  ld x7, 568(x20)
  bltu x7, x6, .exit_outofgas
  sub x7, x7, x6
  sd x7, 568(x20)
  la x6, opcode_handlers
  add x6, x6, x5
  ld x7, 0(x6)
  jalr x1, 0(x7)
