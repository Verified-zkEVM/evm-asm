block_access_list_hash_core:
  addi sp, sp, -16; sd ra, 0(sp)
  jal ra, zkvm_keccak256
  ld ra, 0(sp); addi sp, sp, 16
  ret
