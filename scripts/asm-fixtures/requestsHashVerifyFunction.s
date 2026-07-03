requests_hash_verify:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a6                   # expected hash ptr
  mv s1, a7                   # scratch section buffer
  mv a6, a7                   # assemble out = scratch (a0..a5 still the 3 bodies)
  jal ra, assemble_execution_requests   # a0 = total section length
  mv a1, a0; mv a0, s1; la a2, rhv_hash
  jal ra, execution_requests_hash       # a0 = 0 ok / 1 malformed
  bnez a0, .Lrhv_malformed
  la t0, rhv_hash; mv t1, s0; li t2, 32
.Lrhv_cmp:
  beqz t2, .Lrhv_match
  lbu t3, 0(t0); lbu t4, 0(t1); bne t3, t4, .Lrhv_mismatch
  addi t0, t0, 1; addi t1, t1, 1; addi t2, t2, -1; j .Lrhv_cmp
.Lrhv_match:
  li a0, 0; j .Lrhv_ret
.Lrhv_mismatch:
  li a0, 1; j .Lrhv_ret
.Lrhv_malformed:
  li a0, 2
.Lrhv_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
