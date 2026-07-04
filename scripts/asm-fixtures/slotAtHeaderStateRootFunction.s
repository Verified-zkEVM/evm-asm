slot_at_header_state_root:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)
  sd s8, 72(sp); sd s9, 80(sp)
  mv s0, a0                  # header_rlp ptr
  mv s1, a1                  # header_rlp_len
  mv s2, a2                  # address ptr
  mv s3, a3                  # slot_idx ptr
  mv s4, a4                  # witness.state ptr
  mv s5, a5                  # witness.state len
  mv s6, a6                  # witness.storage ptr
  mv s7, a7                  # witness.storage len
  # Step 1: extract header.state_root -> sahsr_state_root.
  mv a0, s0
  mv a1, s1
  la a2, sahsr_state_root
  jal ra, header_extract_state_root
  beqz a0, .Lsahsr_step2
  li a0, 4
  j .Lsahsr_ret
.Lsahsr_step2:
  # Step 2: account_at_address -> sahsr_acct_struct.
  mv a0, s2
  li a1, 20                  # address byte length
  la a2, sahsr_state_root
  mv a3, s4
  mv a4, s5
  la a5, sahsr_acct_struct
  jal ra, account_at_address
  beqz a0, .Lsahsr_step3
  # a0 is 1/2/3 already; just return it.
  j .Lsahsr_ret
.Lsahsr_step3:
  # Step 3: slot_at_index(slot_idx, 32, &acct.storage_root, witness.storage, ..., sahsr_u256).
  mv a0, s3
  li a1, 32
  la a2, sahsr_acct_struct
  addi a2, a2, 40            # &acct_struct.storage_root
  mv a3, s6
  mv a4, s7
  la a5, sahsr_u256
  jal ra, slot_at_index
  beqz a0, .Lsahsr_ret
  # slot_at_index returned 1/2/3; remap to 5/6/7.
  addi a0, a0, 4
.Lsahsr_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)
  ld s8, 72(sp); ld s9, 80(sp)
  addi sp, sp, 96
  ret
