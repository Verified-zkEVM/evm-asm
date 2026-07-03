headers_validate_chain:
  addi sp, sp, -48
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0                  # s0 = section ptr
  mv s1, a1                  # s1 = section_len
  mv s2, a2                  # s2 = N out ptr
  # Match execution-specs validate_headers: witness headers are capped at
  # 256. Enforce this before filling the fixed 256-entry keccak table.
  beqz s1, .Lvh_count_ok
  lwu t0, 0(s0)
  srli t0, t0, 2             # first inner offset = 4*N
  li t1, 256
  bgtu t0, t1, .Lvh_fail
.Lvh_count_ok:
  # Step 1: keccak each header into vh_keccak_table.
  mv a0, s0
  mv a1, s1
  la a2, vh_keccak_table
  jal ra, headers_keccak_array
  mv s3, a0                  # s3 = N
  sd s3, 0(s2)               # *N_out = N
  # If N ≤ 1, no chain links to check → ok.
  li t0, 2
  bltu s3, t0, .Lvh_ok
  # Loop i = 1..N.
  li s4, 1
.Lvh_loop:
  beq s4, s3, .Lvh_ok
  # Find element i bounds from inner-offset table.
  slli t0, s4, 2             # 4*i
  add t1, s0, t0
  lwu t2, 0(t1)              # inner_off_i
  add a0, s0, t2             # el_i_start
  addi t3, s4, 1
  beq t3, s3, .Lvh_use_end
  slli t3, t3, 2
  add t3, s0, t3
  lwu t4, 0(t3)
  add t4, s0, t4
  j .Lvh_have_end
.Lvh_use_end:
  add t4, s0, s1
.Lvh_have_end:
  sub a1, t4, a0             # el_i_len
  la a2, vh_extracted_parent_hash
  jal ra, headers_parent_hash
  bnez a0, .Lvh_fail         # RLP parse failed
  # Compare extracted parent_hash against vh_keccak_table[i-1].
  la t0, vh_keccak_table
  addi t1, s4, -1
  slli t1, t1, 5             # (i-1) * 32
  add t0, t0, t1             # &table[i-1]
  la t1, vh_extracted_parent_hash
  ld t2,  0(t0); ld t3,  0(t1); bne t2, t3, .Lvh_fail
  ld t2,  8(t0); ld t3,  8(t1); bne t2, t3, .Lvh_fail
  ld t2, 16(t0); ld t3, 16(t1); bne t2, t3, .Lvh_fail
  ld t2, 24(t0); ld t3, 24(t1); bne t2, t3, .Lvh_fail
  addi s4, s4, 1
  j .Lvh_loop
.Lvh_ok:
  li a0, 0
  j .Lvh_ret
.Lvh_fail:
  li a0, 1
.Lvh_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  ld s3, 32(sp); ld s4, 40(sp)
  addi sp, sp, 48
  ret
