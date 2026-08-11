header_extract_base_fee_u64:
  addi x2, x2, -16
  sd x1, 0(x2)
  mv x13, x12
  li x12, 15
  jal x1, rlp_field_to_u64_strict
  ld x1, 0(x2)
  addi x2, x2, 16
  jalr x0, 0(x1)
