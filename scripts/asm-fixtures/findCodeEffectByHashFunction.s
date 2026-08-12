find_code_effect_by_hash:
  addi sp, sp, -80
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp)
  mv s0, a0                   # cursor
  mv s1, a1                   # remaining
  mv s2, a2                   # want hash ptr
.Lfceh_loop:
  beqz s1, .Lfceh_miss
  ld a1, 40(s0)               # code_len
  addi a0, s0, 48             # code bytes
  addi a2, sp, 48             # 32-byte out on stack
  jal ra, zkvm_keccak256
  li t0, 0
.Lfceh_cmp:
  li t1, 32
  beq t0, t1, .Lfceh_hit
  add t2, sp, t0
  lbu t2, 48(t2)
  add t3, s2, t0
  lbu t3, 0(t3)
  bne t2, t3, .Lfceh_next
  addi t0, t0, 1
  j .Lfceh_cmp
.Lfceh_next:
  ld t0, 40(s0)
  addi t0, t0, 55
  andi t0, t0, -8
  add s0, s0, t0
  addi s1, s1, -1
  j .Lfceh_loop
.Lfceh_hit:
  mv a0, s0
  j .Lfceh_ret
.Lfceh_miss:
  li a0, 0
.Lfceh_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp)
  addi sp, sp, 80
  ret
