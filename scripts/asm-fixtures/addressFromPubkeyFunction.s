address_from_pubkey:
  addi sp, sp, -16
  sd ra,  0(sp)
  sd s0,  8(sp)
  mv s0, a1
  li a1, 64
  la a2, afp_digest
  jal ra, zkvm_keccak256
  la t0, afp_digest
  li t1, 0
.Lafp_copy:
  li t2, 20
  beq t1, t2, .Lafp_done
  addi t3, t0, 12
  add t3, t3, t1
  lbu t4, 0(t3)
  add t3, s0, t1
  sb t4, 0(t3)
  addi t1, t1, 1
  j .Lafp_copy
.Lafp_done:
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  addi sp, sp, 16
  ret
