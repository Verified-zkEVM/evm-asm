validate_header_rlp_pair:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  mv s0, a0                  # this_rlp
  mv s1, a1                  # this_len
  mv s2, a2                  # parent_rlp
  mv s3, a3                  # parent_len
  mv a0, s0
  mv a1, s1
  la a2, vhrp_this_struct
  jal ra, header_extended_decode
  bnez a0, .Lvhrp_fail_this
  mv a0, s2
  mv a1, s3
  la a2, vhrp_parent_struct
  jal ra, header_extended_decode
  bnez a0, .Lvhrp_fail_parent
  mv a0, s0
  mv a1, s1
  la a2, vhrp_this_struct
  la a3, vhrp_parent_struct
  mv a4, s2
  mv a5, s3
  jal ra, validate_header
  j .Lvhrp_ret
.Lvhrp_fail_this:
  li a0, 1
  j .Lvhrp_ret
.Lvhrp_fail_parent:
  li a0, 2
.Lvhrp_ret:
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  addi sp, sp, 48
  ret
