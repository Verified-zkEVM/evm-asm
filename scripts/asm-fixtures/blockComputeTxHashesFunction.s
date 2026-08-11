block_compute_tx_hashes:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # txs_list ptr
  mv s1, a1                   # txs_len
  mv s2, a2                   # out hashes buffer
  mv s3, a3                   # out count ptr
  # Step 1: validate the list and initialize its cursor.
  jal ra, rlp_walk_init
  beqz a2, .Lbcth_loop_init
  li a0, 101
  j .Lbcth_ret
.Lbcth_loop_init:
  mv s4, a0                   # cursor
  mv s5, a1                   # end
  li s6, 0                    # N = tx_count
.Lbcth_loop:
  beq s4, s5, .Lbcth_done
  mv a0, s4
  mv a1, s5
  jal ra, rlp_walk_next
  beqz a1, .Lbcth_after_next
  li a0, 201
  j .Lbcth_ret
.Lbcth_after_next:
  mv s4, a0                   # preserve advanced cursor
  sub a0, a0, a2              # tx_ptr = advanced - content_len
  mv a1, a2                   # tx_len
  slli t0, s6, 5              # i × 32
  add a2, s2, t0              # &out[i*32]
  jal ra, zkvm_keccak256
  addi s6, s6, 1
  j .Lbcth_loop
.Lbcth_done:
  sd s6, 0(s3)                # *count = N
  li a0, 0
.Lbcth_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
