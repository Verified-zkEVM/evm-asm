header_extract_excess_blob_gas:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a3, a2
  li a2, 18
  jal ra, rlp_field_to_u64_strict
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
