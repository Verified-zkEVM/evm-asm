tx_validate_against_block:
  bne a0, a1, .Ltvab_fail_chain
  bgtu a2, a3, .Ltvab_fail_gas
  bne a4, a5, .Ltvab_fail_nonce
  li a0, 0
  ret
.Ltvab_fail_chain:
  li a0, 1
  ret
.Ltvab_fail_gas:
  li a0, 2
  ret
.Ltvab_fail_nonce:
  li a0, 3
  ret
