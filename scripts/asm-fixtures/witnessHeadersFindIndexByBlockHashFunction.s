witness_headers_find_index_by_block_hash:
  addi sp, sp, -96
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                  # block_hash ptr
  mv s1, a1                  # section ptr
  mv s2, a2                  # section_len
  mv s3, a3                  # index out
  sd zero, 0(s3)
  sd zero, 64(sp)            # matched offset scratch
  sd zero, 72(sp)            # matched length scratch
  mv a0, s1
  mv a1, s2
  mv a2, s0
  addi a3, sp, 64
  addi a4, sp, 72
  jal ra, witness_lookup_by_hash
  bnez a0, .Lwhfi_miss
  ld s4, 64(sp)              # matched element offset within section
  li t0, 4
  bltu s2, t0, .Lwhfi_miss
  lwu t0, 0(s1)              # first offset = 4 * N
  andi t1, t0, 3
  bnez t1, .Lwhfi_miss
  bgtu t0, s2, .Lwhfi_miss
  srli s5, t0, 2             # s5 = N
  li s6, 0                   # s6 = i
.Lwhfi_loop:
  beq s6, s5, .Lwhfi_miss
  slli t0, s6, 2
  add t1, s1, t0
  lwu t2, 0(t1)              # offset_i
  bgtu t2, s2, .Lwhfi_miss
  beq t2, s4, .Lwhfi_found
  addi s6, s6, 1
  j .Lwhfi_loop
.Lwhfi_found:
  sd s6, 0(s3)
  li a0, 0
  j .Lwhfi_ret
.Lwhfi_miss:
  li a0, 1
.Lwhfi_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 96
  ret
