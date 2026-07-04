verify_public_keys_match_senders:
  addi sp, sp, -80
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  la t0, bv_tx_list_ptr; ld s0, 0(t0)   # SSZ tx list ptr
  la t0, bv_tx_list_len; ld s1, 0(t0)   # tx list byte length
  li t0, 4; bltu s1, t0, .Lvpks_ok      # <4 bytes -> no offset table -> 0 txs
  mv a0, s0; jal ra, bgv_u32le           # offset[0]
  andi t0, a0, 3; bnez t0, .Lvpks_malformed
  srli s2, a0, 2                         # tx_count = offset[0] / 4
  beqz s2, .Lvpks_ok                     # 0-tx block -> nothing to verify
  la t0, bv_public_keys_ptr; ld s3, 0(t0)   # public_keys base (65 bytes/key)
  la t0, bv_chain_id; ld s4, 0(t0)          # execution chain id
  li s5, 0                               # i = 0
.Lvpks_loop:
  beq s5, s2, .Lvpks_ok
  slli t0, s5, 2; add a0, s0, t0; jal ra, bgv_u32le   # offset[i]
  mv s6, a0
  addi t0, s5, 1; beq t0, s2, .Lvpks_last
  slli t1, t0, 2; add a0, s0, t1; jal ra, bgv_u32le   # offset[i+1]
  mv s7, a0
  j .Lvpks_bounds
.Lvpks_last:
  mv s7, s1                              # final tx ends at list end
.Lvpks_bounds:
  slli t0, s2, 2; bltu s6, t0, .Lvpks_malformed   # offset[i] must be past the table
  bltu s7, s6, .Lvpks_malformed                   # offset[i+1] >= offset[i]
  bgtu s7, s1, .Lvpks_malformed                   # offset[i+1] <= list len
  add a0, s0, s6                         # tx[i] ptr
  sub a1, s7, s6                         # tx[i] len
  beqz a1, .Lvpks_malformed              # empty transaction item
  mv a2, s4                              # chain_id
  li t0, 65; mul t0, s5, t0; add a3, s3, t0   # &public_keys[i]
  la a4, vpks_pubkey_out                 # recovered pubkey scratch (64 bytes)
  la a5, vpks_scratch                    # recover scratch (>= 304 bytes)
  jal ra, tx_pubkey_public_key_matches
  bnez a0, .Lvpks_ret                    # mismatch / recovery failure -> reject (propagate)
  addi s5, s5, 1; j .Lvpks_loop
.Lvpks_ok:
  li a0, 0; j .Lvpks_ret
.Lvpks_malformed:
  li a0, 90
.Lvpks_ret:
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  addi sp, sp, 80
  ret
