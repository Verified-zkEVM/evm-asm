header_extract_basefee:
  addi sp, sp, -16
  sd ra, 0(sp)
  # rlp_field_to_u64(a0=header_ptr, a1=len, a2=15, a3=output_ptr)
  mv a3, a2                   # output ptr (caller-supplied) -> a3
  li a2, 15                   # field index = 15 (base_fee)
  jal ra, rlp_field_to_u64_strict
  ld ra, 0(sp)
  addi sp, sp, 16
  ret
