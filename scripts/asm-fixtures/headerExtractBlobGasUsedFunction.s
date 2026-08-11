header_extract_blob_gas_used:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a3, a2
  li a2, 17
  jal ra, rlp_field_to_u64_strict
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
