bal_account_path:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)
  mv s0, a0                   # account-change ptr
  mv s1, a2                   # out path ptr
  # field 0 = address bytes.
  jal ra, rlp_walk_init
  bnez a2, .Lbacp_fail
  jal ra, rlp_walk_next
  bnez a1, .Lbacp_fail
  li t2, 20; bne a2, t2, .Lbacp_fail
  sub a0, a0, a2
  li a1, 20; la a2, bacp_hash
  jal ra, zkvm_keccak256
  la a0, bacp_hash; li a1, 32; mv a2, s1
  jal ra, bytes_to_nibbles
  li a0, 0; j .Lbacp_ret
.Lbacp_fail:
  li a0, 1
.Lbacp_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)
  addi sp, sp, 32
  ret
