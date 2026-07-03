account_set_storage_root:
  addi sp, sp, -48
  sd ra, 0(sp)
  sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                   # account rlp
  mv s1, a1                   # account len
  mv s2, a2                   # new storage_root (32 B)
  mv s3, a3                   # out ptr
  mv s4, a4                   # out len ptr
  # build new_ref = 0xa0 || storage_root (33 B) at asr_ref
  la t0, asr_ref; li t1, 0xa0; sb t1, 0(t0)
  li t2, 0
.Lasr_cp:
  li t3, 32; beq t2, t3, .Lasr_cpdone
  add t4, s2, t2; lbu t5, 0(t4)
  add t6, t0, t2; addi t6, t6, 1; sb t5, 0(t6)
  addi t2, t2, 1; j .Lasr_cp
.Lasr_cpdone:
  # mpt_splice_slot(account, len, 2, asr_ref, 33, out, out_len)
  mv a0, s0; mv a1, s1; li a2, 2
  la a3, asr_ref; li a4, 33
  mv a5, s3; mv a6, s4
  jal ra, mpt_splice_slot
  ld ra, 0(sp)
  ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
