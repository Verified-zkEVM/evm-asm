address_compute_create2:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0
  mv s1, a1
  mv s4, a4
  mv a0, a2
  mv a1, a3
  la a2, ac2_inner_digest
  jal ra, zkvm_keccak256
  la s2, ac2_preimage
  li t0, 0xff
  sb t0, 0(s2)
  li t0, 0
.Lac2_pack_sender:
  li t1, 20
  beq t0, t1, .Lac2_pack_salt
  add t2, s0, t0
  lbu t3, 0(t2)
  addi t2, s2, 1
  add t2, t2, t0
  sb t3, 0(t2)
  addi t0, t0, 1
  j .Lac2_pack_sender
.Lac2_pack_salt:
  li t0, 0
.Lac2_pack_salt_loop:
  li t1, 32
  beq t0, t1, .Lac2_pack_inner
  add t2, s1, t0
  lbu t3, 0(t2)
  addi t2, s2, 21
  add t2, t2, t0
  sb t3, 0(t2)
  addi t0, t0, 1
  j .Lac2_pack_salt_loop
.Lac2_pack_inner:
  la t1, ac2_inner_digest
  li t0, 0
.Lac2_pack_inner_loop:
  li t3, 32
  beq t0, t3, .Lac2_pack_done
  add t2, t1, t0
  lbu t3, 0(t2)
  addi t2, s2, 53
  add t2, t2, t0
  sb t3, 0(t2)
  addi t0, t0, 1
  j .Lac2_pack_inner_loop
.Lac2_pack_done:
  mv a0, s2
  li a1, 85
  la a2, ac2_outer_digest
  jal ra, zkvm_keccak256
  la t0, ac2_outer_digest
  li t1, 0
.Lac2_dig:
  li t2, 20
  beq t1, t2, .Lac2_dig_done
  addi t3, t0, 12
  add t3, t3, t1
  lbu t4, 0(t3)
  add t3, s4, t1
  sb t4, 0(t3)
  addi t1, t1, 1
  j .Lac2_dig
.Lac2_dig_done:
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
