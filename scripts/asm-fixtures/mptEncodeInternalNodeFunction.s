mpt_encode_internal_node:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a2                   # out_bytes ptr
  mv s1, a3                   # out_len ptr
  mv s2, a4                   # is_hashed out
  li t0, 32
  bltu a1, t0, .Lmein_embed
  # Hash path: keccak256(node_rlp, len) → out.
  mv a2, s0
  jal ra, zkvm_keccak256
  li t0, 32
  sd t0, 0(s1)
  li t0, 1
  sd t0, 0(s2)
  li a0, 0
  j .Lmein_ret
.Lmein_embed:
  # Embedded path: copy node_rlp bytes to out_bytes.
  mv t0, a0                   # src cursor
  mv t1, s0                   # dst cursor
  mv t2, a1                   # remaining
.Lmein_copy:
  beqz t2, .Lmein_copy_done
  lbu t3, 0(t0)
  sb t3, 0(t1)
  addi t0, t0, 1
  addi t1, t1, 1
  addi t2, t2, -1
  j .Lmein_copy
.Lmein_copy_done:
  sd a1, 0(s1)
  sd zero, 0(s2)
  li a0, 0
.Lmein_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
