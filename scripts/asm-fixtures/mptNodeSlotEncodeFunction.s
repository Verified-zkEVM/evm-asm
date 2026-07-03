mpt_node_slot_encode:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a2                   # output ptr
  mv s1, a3                   # out_length ptr
  li t0, 32
  bltu a1, t0, .Lmnse_inline
  # Hash path: out[0] = 0xa0; keccak256(node_rlp) -> out[1..33].
  li t1, 0xa0
  sb t1, 0(s0)
  mv s2, a0                   # node_rlp ptr stashed
  # zkvm_keccak256(node_rlp, len, out + 1).
  addi a2, s0, 1
  jal ra, zkvm_keccak256
  li t0, 33
  sd t0, 0(s1)
  li a0, 0
  j .Lmnse_ret
.Lmnse_inline:
  # Inline path: copy node_rlp bytes to out.
  mv t0, a0                   # src cursor
  mv t1, s0                   # dst cursor
  mv t2, a1                   # remaining
.Lmnse_cp:
  beqz t2, .Lmnse_cp_done
  lbu t3, 0(t0)
  sb  t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lmnse_cp
.Lmnse_cp_done:
  sd a1, 0(s1)
  li a0, 0
.Lmnse_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
