eip7702_warm_recovered_authorities:
  addi sp, sp, -64
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp)
  mv s0, a0                    # auth_list ptr
  mv s1, a1                    # auth_list len
  beqz s0, .Le77w_ret
  beqz s1, .Le77w_ret
  la t0, bv_chain_id; ld s4, 0(t0)   # block chain id
  mv a0, s0; mv a1, s1; la a2, e77w_count
  jal ra, rlp_list_count_items
  bnez a0, .Le77w_ret
  la t0, e77w_count; ld s2, 0(t0)    # auth count
  li s3, 0                     # i
.Le77w_loop:
  beq s3, s2, .Le77w_ret
  mv a0, s0; mv a1, s1; mv a2, s3; la a3, e77w_toff; la a4, e77w_tlen
  jal ra, rlp_list_nth_item
  bnez a0, .Le77w_next
  la t0, e77w_toff; ld t1, 0(t0); add s5, s0, t1   # tuple ptr
  la t0, e77w_tlen; ld t2, 0(t0)                   # tuple len (in t-reg, reload before use)
  la t3, e77w_tlen; ld a1, 0(t3); mv a0, s5; li a2, 0; la a3, e77w_chain
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Le77w_next
  la t0, e77w_chain; ld t1, 0(t0); beqz t1, .Le77w_chain_ok; bne t1, s4, .Le77w_next
.Le77w_chain_ok:
  la t3, e77w_tlen; ld a1, 0(t3); mv a0, s5; li a2, 2; la a3, e77w_nonce
  jal ra, rlp_field_to_u64_strict
  bnez a0, .Le77w_next
  la t0, e77w_nonce; ld t1, 0(t0); li t2, -1; beq t1, t2, .Le77w_next
  la t3, e77w_tlen; ld a1, 0(t3); mv a0, s5; la a2, e77w_authority; la a3, e77w_scratch
  jal ra, eip7702_authorization_recover_address
  bnez a0, .Le77w_next
  la a0, e77w_authority; la a1, evm_access_account_table
  la a2, evm_access_account_count; li a3, 100000
  jal ra, runtime_access_account_seed
.Le77w_next:
  addi s3, s3, 1; j .Le77w_loop
.Le77w_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp)
  addi sp, sp, 64
  ret
