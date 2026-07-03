tx_pubkey_ecrecover_stage_material:
  addi sp, sp, -32
  sd s0,  0(sp); sd s1,  8(sp); sd s2, 16(sp); sd s3, 24(sp)
  mv s0, a0                   # material ptr
  mv s1, a1                   # staging ptr
  ld s2, 8(s0)                # recid
  li t0, 1
  bgtu s2, t0, .Ltpes_bad_recid
  # message hash = material.signing_hash
  addi t0, s0, 80
  mv t1, s1
  li t2, 4
.Ltpes_copy_hash:
  ld t3, 0(t0); sd t3, 0(t1)
  addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -1
  bnez t2, .Ltpes_copy_hash
  # signature = r || s
  addi t0, s0, 16
  addi t1, s1, 32
  li t2, 8
.Ltpes_copy_sig:
  ld t3, 0(t0); sd t3, 0(t1)
  addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -1
  bnez t2, .Ltpes_copy_sig
  sd s2, 96(s1)
  addi t1, s1, 104
  li t2, 8
.Ltpes_zero_pubkey:
  sd zero, 0(t1)
  addi t1, t1, 8; addi t2, t2, -1
  bnez t2, .Ltpes_zero_pubkey
  li a0, 0
  j .Ltpes_ret
.Ltpes_bad_recid:
  li a0, 1
.Ltpes_ret:
  ld s0,  0(sp); ld s1,  8(sp); ld s2, 16(sp); ld s3, 24(sp)
  addi sp, sp, 32
  ret
