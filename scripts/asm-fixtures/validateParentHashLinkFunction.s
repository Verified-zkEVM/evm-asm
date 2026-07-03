validate_parent_hash_link:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # parent_rlp ptr
  mv s1, a1                   # parent_rlp len
  mv s2, a2                   # child_rlp ptr
  mv s3, a3                   # child_rlp len
  mv s4, a4                   # is_valid out
  sd zero, 0(s4)
  # ---- Extract child.parent_hash (field 0) ----
  mv a0, s2; mv a1, s3; li a2, 0
  la a3, vphl_offset; la a4, vphl_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lvphl_parse_fail
  la t0, vphl_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lvphl_size_fail
  # Copy claimed parent_hash into vphl_claimed
  la t0, vphl_offset; ld t1, 0(t0)
  add t3, s2, t1                              # &child[off]
  la t4, vphl_claimed
  ld t5,  0(t3); sd t5,  0(t4)
  ld t5,  8(t3); sd t5,  8(t4)
  ld t5, 16(t3); sd t5, 16(t4)
  ld t5, 24(t3); sd t5, 24(t4)
  # ---- Compute keccak256(parent_rlp) ----
  mv a0, s0; mv a1, s1
  la a2, vphl_computed
  jal ra, block_hash_from_header
  # ---- 32-byte compare ----
  la t0, vphl_claimed
  la t1, vphl_computed
  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvphl_neq
  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvphl_neq
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvphl_neq
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvphl_neq
  li t0, 1
  sd t0, 0(s4)
  li a0, 0
  j .Lvphl_ret
.Lvphl_neq:
  sd zero, 0(s4)
  li a0, 0
  j .Lvphl_ret
.Lvphl_parse_fail:
  li a0, 1
  j .Lvphl_ret
.Lvphl_size_fail:
  li a0, 2
.Lvphl_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
