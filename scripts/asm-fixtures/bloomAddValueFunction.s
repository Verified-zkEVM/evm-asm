bloom_add_value:
  addi sp, sp, -32
  sd ra,  0(sp)
  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp)
  mv s0, a0                   # bloom ptr
  mv s1, a1                   # value ptr
  mv s2, a2                   # value len
  # ---- Compute keccak256(value) → bav_hash ----
  mv a0, s1; mv a1, s2
  la a2, bav_hash
  jal ra, zkvm_keccak256
  # ---- Set three bits derived from h[0..6] ----
  la t0, bav_hash
  li t1, 0                    # idx loop counter (0, 2, 4)
.Lbav_loop:
  li t2, 6
  bge t1, t2, .Lbav_done
  add t3, t0, t1
  lbu t4, 0(t3)               # hi byte
  lbu t5, 1(t3)               # lo byte
  slli t4, t4, 8
  or  t4, t4, t5              # raw_word
  li  t5, 0x7ff
  and t4, t4, t5              # raw_bit (0..2047)
  sub t4, t5, t4              # bit_index = 0x7ff - raw_bit
  srli t5, t4, 3              # byte_index = bit_index / 8
  andi t6, t4, 7              # bit_index mod 8
  li  t4, 7
  sub t6, t4, t6              # bit_pos = 7 - (bit_index mod 8)
  li  t4, 1
  sll t6, t4, t6              # bit_mask = 1 << bit_pos
  add t5, s0, t5              # &bloom[byte_index]
  lbu t4, 0(t5)
  or  t4, t4, t6
  sb  t4, 0(t5)
  addi t1, t1, 2
  j .Lbav_loop
.Lbav_done:
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp)
  addi sp, sp, 32
  ret
