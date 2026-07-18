tx_intrinsic_state_gas:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # tx_ptr
  mv s1, a1                   # tx_len
  mv s2, a2                   # out ptr
  # is_creation via K101 (handles per-type `to` field index)
  mv a0, s0; mv a1, s1; la a2, tis_to_buf; la a3, tis_is_creation
  jal ra, tx_extract_to_address
  bnez a0, .Ltisg_fail1
  # tx type + inner-RLP offset (for the EIP-7702 authorization_list)
  mv a0, s0; mv a1, s1; la a2, tis_type; la a3, tis_inner_off
  jal ra, tx_type_dispatch
  bnez a0, .Ltisg_fail2
  li s4, 0                    # intrinsic_state_gas accumulator
  # tx_state_gas = eip8037_tx_state_gas(intrinsic, 0)
  mv a0, s4; li a1, 0; li a2, 0; li a3, 0
  la t0, tis_is_creation; ld a4, 0(t0)
  mv a5, s2
  jal ra, eip8037_tx_state_gas
  j .Ltisg_ret
.Ltisg_fail1:
  li a0, 1; sd zero, 0(s2); j .Ltisg_ret
.Ltisg_fail2:
  li a0, 2; sd zero, 0(s2)
.Ltisg_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
