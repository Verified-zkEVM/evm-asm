tx_pubkey_recover_raw:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # tx ptr
  mv s1, a1                   # tx len
  mv s2, a2                   # chain_id
  mv s3, a3                   # recovered pubkey out
  mv s4, a4                   # scratch ptr
  # build signature material into scratch+8
  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s4, 8
  jal ra, tx_pubkey_signature_material
  sd a0, 0(s4)                # record material status in side slot
  beqz a0, .Ltprr_material_ok
  li a0, 10
  j .Ltprr_ret
.Ltprr_material_ok:
  # stage material into ecrecover ABI at scratch+136
  addi a0, s4, 8; addi a1, s4, 136
  jal ra, tx_pubkey_ecrecover_stage_material
  beqz a0, .Ltprr_stage_ok
  li a0, 20
  j .Ltprr_ret
.Ltprr_stage_ok:
  # --- secp256k1 public-key recovery over the staged ABI block ---
  # (extracted as secp256k1_recover_pubkey_staged so the ECRECOVER
  #  precompile can reuse it; .62.2.5)
  addi a0, s4, 136            # staged ABI block ptr
  mv a1, s3                   # recovered pubkey out
  jal ra, secp256k1_recover_pubkey_staged
  beqz a0, .Ltprr_ok
  li a0, 60
  j .Ltprr_ret
.Ltprr_ok:
  li a0, 0
  j .Ltprr_ret
.Ltprr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
