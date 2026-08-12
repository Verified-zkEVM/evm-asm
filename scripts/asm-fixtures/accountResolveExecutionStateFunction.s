account_resolve_execution_state:
  addi sp, sp, -208
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4; mv s5, a5; mv s6, a6; mv s7, a7; li s8, 0
  mv a0, s0; jal ra, account_read_record
  sd zero, 0(s1); sd zero, 8(s1); sd zero, 16(s1); sd zero, 24(s1); sd zero, 32(s1); sd zero, 40(s1); sd zero, 48(s1); sd zero, 56(s1)
  la t0, tx_account_writes_count; ld t1, 0(t0); li t2, 0xbf780000; li t3, 0
.Lare_tx_scan:
  bgeu t3, t1, .Lare_tx_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0
.Lare_tx_cmp:
  beqz t6, .Lare_tx_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lare_tx_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lare_tx_cmp
.Lare_tx_next:
  addi t3, t3, 1; j .Lare_tx_scan
.Lare_tx_hit:
  mv t6, t5; ld t0, 112(t6); andi t1, t0, 1; beqz t1, .Lare_tx_nonce; ld t1, 32(t6); sd t1, 8(s1); ld t1, 40(t6); sd t1, 16(s1); ld t1, 48(t6); sd t1, 24(s1); ld t1, 56(t6); sd t1, 32(s1); ori s8, s8, 1
.Lare_tx_nonce:
  andi t1, t0, 2; beqz t1, .Lare_tx_code; ld t1, 64(t6); sd t1, 0(s1); ori s8, s8, 2
.Lare_tx_code:
  andi t1, t0, 4; beqz t1, .Lare_tx_state; ld t1, 80(t6); sd t1, 40(s1); ld t1, 88(t6); sd t1, 48(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 4
.Lare_tx_state:
  andi t1, t0, 8; beqz t1, .Lare_tx_done; ld t1, 72(t6); sd t1, 56(s1); ori s8, s8, 8
.Lare_tx_done:
  andi t0, s8, 8; beqz t0, .Lare_block_scan
  ld t1, 56(s1); beqz t1, .Lare_deleted
.Lare_block_scan:
  la t0, account_writes_count; ld t1, 0(t0); li t2, 0xbdb80000; li t3, 0
.Lare_block_loop:
  bgeu t3, t1, .Lare_block_done; slli t4, t3, 7; add t5, t2, t4; li t6, 20; mv a0, t5; mv a1, s0
.Lare_block_cmp:
  beqz t6, .Lare_block_hit; lbu a2, 0(a0); lbu a3, 0(a1); bne a2, a3, .Lare_block_next; addi a0, a0, 1; addi a1, a1, 1; addi t6, t6, -1; j .Lare_block_cmp
.Lare_block_next:
  addi t3, t3, 1; j .Lare_block_loop
.Lare_block_hit:
  mv t6, t5; ld t0, 112(t6); andi t1, s8, 4; bnez t1, .Lare_block_state; andi t1, t0, 4; beqz t1, .Lare_block_state; ld t1, 80(t6); sd t1, 40(s1); ld t1, 88(t6); sd t1, 48(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 4
.Lare_block_state:
  andi t1, s8, 8; bnez t1, .Lare_block_done; andi t1, t0, 8; beqz t1, .Lare_block_done; ld t1, 72(t6); sd t1, 56(s1); ori s8, s8, 8
.Lare_block_done:
  andi t0, s8, 8; beqz t0, .Lare_parent
  ld t1, 56(s1); beqz t1, .Lare_deleted
  andi t0, s8, 4; bnez t0, .Lare_classify_code
.Lare_parent:
  mv a0, s0; addi a1, sp, 96; mv a2, s2; mv a3, s3; mv a4, s4; mv a5, s5; jal ra, account_resolve_pre_state
  bnez a0, .Lare_malformed
  andi t0, s8, 1; bnez t0, .Lare_nonce
  addi t1, sp, 96; ld t2, 8(t1); sd t2, 8(s1); ld t2, 16(t1); sd t2, 16(s1); ld t2, 24(t1); sd t2, 24(s1); ld t2, 32(t1); sd t2, 32(s1); ori s8, s8, 1
.Lare_nonce:
  andi t0, s8, 2; bnez t0, .Lare_code_source; addi t1, sp, 96; ld t2, 0(t1); sd t2, 0(s1); ori s8, s8, 2
.Lare_code_source:
  andi t0, s8, 4; bnez t0, .Lare_classify_code
  mv a0, s2; mv a1, s3; mv a2, s0; li a3, 20; mv a4, s4; mv a5, s5; addi a6, sp, 96; jal ra, account_at_header_state_root_tracked
  beqz a0, .Lare_parent_found; li t0, 1; beq a0, t0, .Lare_absent; j .Lare_malformed
.Lare_parent_found:
  andi t0, s8, 8; bnez t0, .Lare_code_hash; addi t3, sp, 96; ld t1, 0(t3); sd t1, 0(s1); ld t1, 8(t3); sd t1, 8(s1); ld t1, 16(t3); sd t1, 16(s1); ld t1, 24(t3); sd t1, 24(s1); ld t1, 32(t3); sd t1, 32(s1); li t1, 1; sd t1, 56(s1); ori s8, s8, 3
.Lare_code_hash:
  addi t3, sp, 96; la t0, chahsr_empty_code_hash; ld t1, 72(t3); ld t2, 0(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 80(t3); ld t2, 8(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 88(t3); ld t2, 16(t0); bne t1, t2, .Lare_hash_nonempty; ld t1, 96(t3); ld t2, 24(t0); bne t1, t2, .Lare_hash_nonempty; j .Lare_empty
.Lare_hash_nonempty:
  mv a0, s6; mv a1, s7; addi a2, sp, 168; addi a3, sp, 80; addi a4, sp, 88; sd zero, 80(sp); sd zero, 88(sp); jal ra, witness_codes_lookup_by_hash
  bnez a0, .Lare_unavailable; ld t0, 80(sp); add t0, s6, t0; sd t0, 40(s1); ld t1, 88(sp); sd t1, 48(s1); j .Lare_classify_code
.Lare_classify_code:
  ld t0, 48(s1); li t1, 3; bltu t0, t1, .Lare_classify_plain; ld t0, 40(s1); lbu t1, 0(t0); li t2, 0xef; bne t1, t2, .Lare_classify_plain; lbu t1, 1(t0); li t2, 1; bne t1, t2, .Lare_classify_plain; lbu t1, 2(t0); bnez t1, .Lare_classify_plain; j .Lare_classify_marker
.Lare_classify_marker:
  li a0, 1; j .Lare_ret
.Lare_classify_plain:
  ld t0, 48(s1); beqz t0, .Lare_empty; li a0, 1; j .Lare_ret
.Lare_empty:
  sd zero, 40(s1); sd zero, 48(s1); li a0, 2; j .Lare_ret
.Lare_absent:
  andi t0, s8, 8; beqz t0, .Lare_absent_zero; ld t1, 56(s1); bnez t1, .Lare_empty
.Lare_absent_zero:
  sd zero, 40(s1); sd zero, 48(s1); li a0, 0; j .Lare_ret
.Lare_deleted:
  sd zero, 40(s1); sd zero, 48(s1); li a0, 3; j .Lare_ret
.Lare_unavailable:
  sd zero, 40(s1); sd zero, 48(s1); li a0, 4; j .Lare_ret
.Lare_malformed:
  sd zero, 40(s1); sd zero, 48(s1); li a0, 5
.Lare_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp); addi sp, sp, 208; ret
