bal_account_has_state_change:
  addi sp, sp, -32
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0; mv s1, a1
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_init
  bnez a2, .Lbahsc_parse_fail
  mv s0, a0                    # AccountChanges cursor
  mv s1, a1                    # AccountChanges end
  jal ra, rlp_walk_next        # item 0: address
  bnez a1, .Lbahsc_parse_fail
  mv s0, a0
  jal ra, .Lbahsc_check_next   # item 1: storage_changes
  mv a0, s0; mv a1, s1
  jal ra, rlp_walk_next        # item 2: storage_reads (read-only)
  bnez a1, .Lbahsc_parse_fail
  mv s0, a0
  jal ra, .Lbahsc_check_next   # item 3: balance_changes
  jal ra, .Lbahsc_check_next   # item 4: nonce_changes
  jal ra, .Lbahsc_check_next   # item 5: code_changes
  li a0, 0; j .Lbahsc_ret
# Consume the next AccountChanges field and return if its sub-list is empty.
# Branches directly to changed/parse-fail for the non-empty/fail outcomes.
.Lbahsc_check_next:
  mv s2, ra
  mv a0, s0; mv a1, s1; jal ra, rlp_walk_next
  bnez a1, .Lbahsc_parse_fail
  mv s0, a0                    # advance AccountChanges cursor
  sub a0, a0, a2; mv a1, a2; jal ra, rlp_walk_init
  bnez a2, .Lbahsc_parse_fail
  bne a0, a1, .Lbahsc_changed
  mv ra, s2; ret
.Lbahsc_changed:
  li a0, 1; j .Lbahsc_ret
.Lbahsc_parse_fail:
  li a0, 2
.Lbahsc_ret:
  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
