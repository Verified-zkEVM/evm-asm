block_compute_tx_hashes:
  addi x2, x2, -64
  sd x1, 0(x2)
  sd x8, 8(x2)
  sd x9, 16(x2)
  sd x18, 24(x2)
  sd x19, 32(x2)
  sd x20, 40(x2)
  sd x21, 48(x2)
  sd x22, 56(x2)
  mv x8, x10
  mv x9, x11
  mv x18, x12
  mv x19, x13
  jal x1, rlp_walk_init
  beq x12, x0, .+12
  li x10, 101
  jal x0, .+84
  mv x20, x10
  mv x21, x11
  li x22, 0
  beq x20, x21, .+60
  mv x10, x20
  mv x11, x21
  jal x1, rlp_walk_next
  beq x11, x0, .+12
  li x10, 201
  jal x0, .+44
  mv x20, x10
  sub x10, x10, x12
  mv x11, x12
  slli x5, x22, 5
  add x12, x18, x5
  jal x1, zkvm_keccak256
  addi x22, x22, 1
  jal x0, .-56
  sd x22, 0(x19)
  li x10, 0
  ld x1, 0(x2)
  ld x8, 8(x2)
  ld x9, 16(x2)
  ld x18, 24(x2)
  ld x19, 32(x2)
  ld x20, 40(x2)
  ld x21, 48(x2)
  ld x22, 56(x2)
  addi x2, x2, 64
  jalr x0, 0(x1)
