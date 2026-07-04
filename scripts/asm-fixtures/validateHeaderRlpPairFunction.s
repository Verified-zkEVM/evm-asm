validate_header_rlp_pair:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  mv s0, a0                   # this rlp
  mv s1, a1                   # this len
  mv s2, a2                   # parent rlp
  mv s3, a3                   # parent len
  # decode this header -> vhrp_this_struct (144 B).
  la a2, vhrp_this_struct
  jal ra, header_extended_decode
  bnez a0, .Lvhrp_this_parse
  # decode parent header -> vhrp_parent_struct.
  mv a0, s2; mv a1, s3; la a2, vhrp_parent_struct
  jal ra, header_extended_decode
  bnez a0, .Lvhrp_parent_parse
  # full field validation (this vs parent).
  mv a0, s0; mv a1, s1
  la a2, vhrp_this_struct; la a3, vhrp_parent_struct
  jal ra, validate_header_full
  bnez a0, .Lvhrp_ret         # already >=100, decade-encoded
  # parent_hash linkage: this.parent_hash == keccak256(parent_rlp).
  mv a0, s0; mv a1, s1; mv a2, s2; mv a3, s3
  jal ra, header_validate_parent_hash
  beqz a0, .Lvhrp_ret         # 0 = valid
  addi a0, a0, 700            # 701 parse / 702 mismatch
  j .Lvhrp_ret
.Lvhrp_this_parse:
  li a0, 1
  j .Lvhrp_ret
.Lvhrp_parent_parse:
  li a0, 2
.Lvhrp_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  addi sp, sp, 48
  ret
