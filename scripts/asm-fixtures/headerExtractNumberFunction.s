header_extract_number:
  addi sp, sp, -16
  sd ra, 0(sp)
  mv a3, a2
  li a2, 8
  jal ra, rlp_field_to_u64
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
