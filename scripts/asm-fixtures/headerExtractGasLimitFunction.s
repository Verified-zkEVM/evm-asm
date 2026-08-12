header_extract_gas_limit:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a3, a2
  li a2, 9
  jal ra, rlp_field_to_u64_strict
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
