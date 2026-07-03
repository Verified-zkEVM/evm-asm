derive_chain_id_from_v:
  li t0, 27
  beq a0, t0, .Ldcid_pre155
  li t0, 28
  beq a0, t0, .Ldcid_pre155
  # EIP-155: chain_id = (v - 35) / 2
  addi t1, a0, -35
  srli t1, t1, 1
  sd t1, 0(a1)
  li t2, 1
  sd t2, 0(a2)
  li a0, 0
  ret
.Ldcid_pre155:
  sd zero, 0(a1)
  sd zero, 0(a2)
  li a0, 0
  ret
