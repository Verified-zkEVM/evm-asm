bal_account_nonstorage_finals:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # AccountChanges ptr
  mv s1, a1                   # AccountChanges len
  mv s2, a2                   # out ptr
  sd zero, 0(s2); sd zero, 40(s2); sd zero, 56(s2); sd zero, 64(s2); sd zero, 72(s2)
  sd zero, 8(s2); sd zero, 16(s2); sd zero, 24(s2); sd zero, 32(s2); sd zero, 48(s2)
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  sd a0, 48(sp); sd a1, 56(sp)
  # Skip address, storage_changes, storage_reads.
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 48(sp)
  # --- balance_changes = item 3; final post_balance = item 1 of its last tuple ---
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sd a0, 48(sp); sub s3, a0, a2; mv s4, a2
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  beq a0, a1, .Lc2nsf_nonce
  sd a0, 64(sp); sd a1, 72(sp)
.Lc2nsf_balance_last_loop:
  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_balance_have_last
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2
  j .Lc2nsf_balance_last_loop
.Lc2nsf_balance_have_last:
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  sd a0, 64(sp); sd a1, 72(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sub a0, a0, a2; mv a1, a2; addi a2, s2, 8; jal ra, rlp_content_to_u256_be
  bnez a0, .Lc2nsf_fail
  li t0, 1; sd t0, 0(s2)
  # --- nonce_changes = item 4; final new_nonce = item 1 of its last tuple (u64) ---
.Lc2nsf_nonce:
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sd a0, 48(sp); sub s3, a0, a2; mv s4, a2
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  beq a0, a1, .Lc2nsf_code
  sd a0, 64(sp); sd a1, 72(sp)
.Lc2nsf_nonce_last_loop:
  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_nonce_have_last
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2
  j .Lc2nsf_nonce_last_loop
.Lc2nsf_nonce_have_last:
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  sd a0, 64(sp); sd a1, 72(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_content_to_u64
  bnez a1, .Lc2nsf_fail
  sd a0, 48(s2)
  li t0, 1; sd t0, 40(s2)
  # --- code_changes = item 5; locate item 1 of its last tuple (no conversion) ---
.Lc2nsf_code:
  ld a0, 48(sp); ld a1, 56(sp); jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sub s3, a0, a2; mv s4, a2
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  beq a0, a1, .Lc2nsf_ok
  sd a0, 64(sp); sd a1, 72(sp)
.Lc2nsf_code_last_loop:
  ld t0, 64(sp); ld t1, 72(sp); beq t0, t1, .Lc2nsf_code_have_last
  mv a0, t0; mv a1, t1; jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sd a0, 64(sp); sub s3, a0, a2; mv s4, a2
  j .Lc2nsf_code_last_loop
.Lc2nsf_code_have_last:
  mv a0, s3; mv a1, s4; jal ra, rlp_walk_init
  bnez a2, .Lc2nsf_fail
  sd a0, 64(sp); sd a1, 72(sp)
  ld a0, 64(sp); ld a1, 72(sp); jal ra, rlp_walk_next; bnez a1, .Lc2nsf_fail; sd a0, 64(sp)
  ld t3, 64(sp); ld a1, 72(sp); mv a0, t3; jal ra, rlp_walk_next
  bnez a1, .Lc2nsf_fail
  sub t4, a0, a2; sub t4, t4, s0; sd t4, 64(s2)
  sd a2, 72(s2)
  li t0, 1; sd t0, 56(s2)
.Lc2nsf_ok:
  li a0, 0; j .Lc2nsf_ret
.Lc2nsf_fail:
  li a0, 1
.Lc2nsf_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 80
  ret
