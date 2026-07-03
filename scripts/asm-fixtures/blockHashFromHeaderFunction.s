block_hash_from_header:
  addi sp, sp, -16
  sd ra, 0(sp)
  # zkvm_keccak256(a0=header, a1=len, a2=out)
  jal ra, zkvm_keccak256
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
