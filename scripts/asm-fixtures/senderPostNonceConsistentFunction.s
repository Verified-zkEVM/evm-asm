sender_post_nonce_consistent:
  ld t0, 128(a0)              # post nonce byte length
  li t1, -1; beq t0, t1, .Lspnc_skip       # absent -> skip
  li t1, 8;  bgtu t0, t1, .Lspnc_skip       # > u64 -> skip
  addi t2, a0, 136; li t3, 0; mv t4, t0     # decode big-endian post nonce
.Lspnc_be:
  beqz t4, .Lspnc_de
  slli t3, t3, 8; lbu t5, 0(t2); or t3, t3, t5; addi t2, t2, 1; addi t4, t4, -1; j .Lspnc_be
.Lspnc_de:
  ld t4, 80(a0); addi t4, t4, 1             # expected = pre nonce + 1
  beq t3, t4, .Lspnc_match
  li a0, 1; ret                             # mismatch
.Lspnc_match:
  li a0, 0; ret
.Lspnc_skip:
  li a0, 2; ret
