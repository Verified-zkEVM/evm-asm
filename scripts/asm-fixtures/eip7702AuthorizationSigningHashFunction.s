eip7702_authorization_signing_hash:
  addi sp, sp, -16
  sd ra,  0(sp)
  # Forward to tx_signing_hash with n=3, type_prefix=0x05.
  # a0 = inner_rlp ptr      (unchanged)
  # a1 = inner_rlp byte len (unchanged)
  # a2 = 32-byte output ptr (move to a4 per K145 ABI)
  mv a4, a2
  li a2, 3                  # n_fields
  li a3, 0x05               # MAGIC type prefix
  jal ra, tx_signing_hash
  ld ra,  0(sp)
  addi sp, sp, 16
  ret
