runtime_same_block_delegation_code:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0
  jal ra, account_state_lookup_current
  li t0, 2; beq a0, t0, .Lrsbd_empty_hit
  li t0, 1; bne a0, t0, .Lrsbd_miss
  mv s1, a1; mv s2, a2
  beqz s2, .Lrsbd_empty_hit
  li t0, 23; bne s2, t0, .Lrsbd_miss
  lbu t0, 0(s1); li t1, 0xef; bne t0, t1, .Lrsbd_miss
  lbu t0, 1(s1); li t1, 1; bne t0, t1, .Lrsbd_miss
  lbu t0, 2(s1); bnez t0, .Lrsbd_miss
  la t0, rsbd_code_ptr; sd s1, 0(t0)
  la t0, rsbd_code_len; sd s2, 0(t0)
  li a0, 0; j .Lrsbd_ret
.Lrsbd_empty_hit:
  la t0, rsbd_code_ptr; sd zero, 0(t0)
  la t0, rsbd_code_len; sd zero, 0(t0)
  li a0, 0; j .Lrsbd_ret
.Lrsbd_miss:
  li a0, 1
.Lrsbd_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32; ret
