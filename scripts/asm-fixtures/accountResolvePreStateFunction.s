account_resolve_pre_state:
  addi sp, sp, -208
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; li s7, 0
  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1); sd zero, 32(s1)
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Larp_block_scan:
  bgeu t3, t1, .Larp_block_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0
.Larp_block_cmp:
  beqz t6, .Larp_block_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Larp_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Larp_block_cmp
.Larp_block_next:
  addi t3, t3, 1; j .Larp_block_scan
.Larp_block_hit:
  mv s6, t5; ld t0, 112(s6); andi t1, t0, 1; beqz t1, .Larp_block_nonce; ld t1, 32(s6); sd t1, 8(s1); ld t1, 40(s6); sd t1, 16(s1); ld t1, 48(s6); sd t1, 24(s1); ld t1, 56(s6); sd t1, 32(s1); ori s7, s7, 1
.Larp_block_nonce:
  andi t1, t0, 2; beqz t1, .Larp_block_done; ld t1, 64(s6); sd t1, 0(s1); ori s7, s7, 2
.Larp_block_done:
.Larp_header_done:
  li t0, 3; beq s7, t0, .Larp_ok
  mv a0, s2; mv a1, s3; mv a2, s0; li a3, 20; mv a4, s4; mv a5, s5; addi a6, sp, 96; jal ra, account_at_header_state_root_tracked
  li t0, 1; bgtu a0, t0, .Larp_fail; beqz a0, .Larp_header_found; j .Larp_ok
.Larp_header_found:
  andi t1, s7, 1; bnez t1, .Larp_header_nonce; addi t0, sp, 96; ld t1, 8(t0); sd t1, 8(s1); ld t1, 16(t0); sd t1, 16(s1); ld t1, 24(t0); sd t1, 24(s1); ld t1, 32(t0); sd t1, 32(s1); ori s7, s7, 1
.Larp_header_nonce:
  andi t1, s7, 2; bnez t1, .Larp_ok; addi t0, sp, 96; ld t1, 0(t0); sd t1, 0(s1); ori s7, s7, 2
.Larp_ok:
  li a0, 0; j .Larp_ret
.Larp_fail:
  li a0, 1
.Larp_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 208; ret
