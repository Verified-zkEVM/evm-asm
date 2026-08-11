chain_validate_post_merge_full:
  addi sp, sp, -56
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0; mv s1, a1; mv s2, a2; mv s3, a3; mv s4, a4
  li t0, 1
  sd t0, 0(s3); sd zero, 0(s4)
  li s5, 0
.Lcvpmf_loop:
  beq s5, s0, .Lcvpmf_done
  la t0, cvpmf_iter_ptr; sd s2, 0(t0)
  la t0, cvpmf_iter_i;   sd s5, 0(t0)
  # (1) difficulty (field 7) -- must be 0
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 7
  la a3, cvpmf_field
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Lcvpmf_propagate
  la t0, cvpmf_field; ld t1, 0(t0)
  bnez t1, .Lcvpmf_diff_fail
  # (2) nonce (field 14) -- must be 0
  la t0, cvpmf_iter_ptr; ld s2, 0(t0)
  la t0, cvpmf_iter_i;   ld s5, 0(t0)
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 14
  la a3, cvpmf_field
  jal ra, rlp_field_to_u64
  bnez a0, .Lcvpmf_propagate
  la t0, cvpmf_field; ld t1, 0(t0)
  bnez t1, .Lcvpmf_nonce_fail
  # (3) ommers_hash (field 1, 32B) -- must equal EMPTY_LIST_KECCAK
  la t0, cvpmf_iter_ptr; ld s2, 0(t0)
  la t0, cvpmf_iter_i;   ld s5, 0(t0)
  slli t3, s5, 3
  add t3, s1, t3
  ld a1, 0(t3)
  mv a0, s2; li a2, 1
  la a3, cvpmf_offset; la a4, cvpmf_length
  jal ra, rlp_list_nth_item
  bnez a0, .Lcvpmf_propagate
  la t0, cvpmf_length; ld t1, 0(t0)
  li t2, 32
  bne t1, t2, .Lcvpmf_size_fail
  la t0, cvpmf_iter_ptr; ld s2, 0(t0)
  la t0, cvpmf_iter_i;   ld s5, 0(t0)
  la t0, cvpmf_offset; ld t1, 0(t0)
  add t2, s2, t1
  la t3, cvpmf_empty_hash
  ld t4,  0(t2); ld t5,  0(t3); bne t4, t5, .Lcvpmf_omh_fail
  ld t4,  8(t2); ld t5,  8(t3); bne t4, t5, .Lcvpmf_omh_fail
  ld t4, 16(t2); ld t5, 16(t3); bne t4, t5, .Lcvpmf_omh_fail
  ld t4, 24(t2); ld t5, 24(t3); bne t4, t5, .Lcvpmf_omh_fail
  # All three checks pass; advance to next header
  slli t3, s5, 3
  add t3, s1, t3
  ld t4, 0(t3)
  add s2, s2, t4
  addi s5, s5, 1
  j .Lcvpmf_loop
.Lcvpmf_diff_fail:
  slli t2, s5, 2; ori t2, t2, 1
  sd zero, 0(s3); sd t2, 0(s4)
  li a0, 0
  j .Lcvpmf_ret
.Lcvpmf_nonce_fail:
  slli t2, s5, 2; ori t2, t2, 2
  sd zero, 0(s3); sd t2, 0(s4)
  li a0, 0
  j .Lcvpmf_ret
.Lcvpmf_omh_fail:
  slli t2, s5, 2; ori t2, t2, 3
  sd zero, 0(s3); sd t2, 0(s4)
  li a0, 0
  j .Lcvpmf_ret
.Lcvpmf_size_fail:
  la t0, cvpmf_iter_i; ld t1, 0(t0)
  slli t2, t1, 2; ori t2, t2, 3
  sd t2, 0(s4)
  li a0, 3
  j .Lcvpmf_ret
.Lcvpmf_propagate:
  la t0, cvpmf_iter_i; ld t1, 0(t0)
  sd t1, 0(s4)
  j .Lcvpmf_ret
.Lcvpmf_done:
  li a0, 0
.Lcvpmf_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 56
  ret
