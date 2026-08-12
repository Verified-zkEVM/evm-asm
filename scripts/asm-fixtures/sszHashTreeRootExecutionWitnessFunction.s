ssz_hash_tree_root_execution_witness:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)
  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)
  mv s0, a0                   # s0 = section ptr
  mv s1, a1                   # s1 = section_len
  mv s2, a2                   # s2 = out ptr
  lwu s3, 0(s0)               # off_state
  lwu s4, 4(s0)               # off_codes
  lwu s5, 8(s0)               # off_headers
  add s6, s0, s1              # section_end
  # Field 0: state (List[ByteList[2^10], 2^22]; byte_log2=5, count_log2=22)
  add a0, s0, s3              # state_start
  add t0, s0, s4              # state_end
  sub a1, t0, a0
  li a2, 5
  li a3, 22
  la a4, ssz_ew_field_roots
  jal ra, ssz_hash_tree_root_list_bytelist
  bnez a0, .Lszew_ret
  # Field 1: codes (List[ByteList[2^16], 2^18]; byte_log2=11, count_log2=18)
  add a0, s0, s4              # codes_start
  add t0, s0, s5              # codes_end
  sub a1, t0, a0
  li a2, 11
  li a3, 18
  la a4, ssz_ew_field_roots
  addi a4, a4, 32
  jal ra, ssz_hash_tree_root_list_bytelist
  bnez a0, .Lszew_ret
  # Field 2: headers (List[ByteList[2^10], 2^8]; byte_log2=5, count_log2=8)
  add a0, s0, s5              # headers_start
  sub a1, s6, a0
  li a2, 5
  li a3, 8
  la a4, ssz_ew_field_roots
  addi a4, a4, 64
  jal ra, ssz_hash_tree_root_list_bytelist
  bnez a0, .Lszew_ret
  # Merkleize 3 field roots, capacity = 4 slots (limit_log2 = 2)
  la a0, ssz_ew_field_roots
  li a1, 3
  li a2, 2
  mv a3, s2
  jal ra, ssz_merkleize
  li a0, 0
.Lszew_ret:
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)
  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)
  addi sp, sp, 64
  ret
