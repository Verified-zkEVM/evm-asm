ssz_merkleize_pow2:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  sd s6, 56(sp)
  # s0 = n (current chunk count); s5 = scratch base; s6 = caller out ptr
  mv s0, a1
  mv s6, a2
  la s5, ssz_merkleize_scratch
  # copy n*32 input bytes into scratch (in 8-byte units)
  mv t0, a0
  mv t1, s5
  slli t2, s0, 5             # t2 = n * 32 bytes to copy
.Lmrk_copy:
  beqz t2, .Lmrk_iter
  ld t3, 0(t0)
  sd t3, 0(t1)
  addi t0, t0, 8
  addi t1, t1, 8
  addi t2, t2, -8
  j .Lmrk_copy
.Lmrk_iter:
  # if n == 1: root is at scratch[0..32]
  li t0, 1
  beq s0, t0, .Lmrk_done
  # pair-hash adjacent chunks into the lower half of scratch
  srli s1, s0, 1             # s1 = n/2 = pair count
  mv s2, s5                  # s2 = src pair ptr (64-byte step)
  mv s3, s5                  # s3 = dst slot ptr (32-byte step)
.Lmrk_pair:
  beqz s1, .Lmrk_advance
  mv a0, s2
  mv a2, s3
  li a1, 64
  jal ra, zkvm_sha256
  addi s2, s2, 64
  addi s3, s3, 32
  addi s1, s1, -1
  j .Lmrk_pair
.Lmrk_advance:
  srli s0, s0, 1             # n /= 2
  j .Lmrk_iter
.Lmrk_done:
  # copy 32 bytes scratch[0..32] -> caller out ptr (s6)
  ld t0,  0(s5);  sd t0,  0(s6)
  ld t0,  8(s5);  sd t0,  8(s6)
  ld t0, 16(s5);  sd t0, 16(s6)
  ld t0, 24(s5);  sd t0, 24(s6)
  li a0, 0
  ld ra,  0(sp)
  ld s0,  8(sp)
  ld s1, 16(sp)
  ld s2, 24(sp)
  ld s3, 32(sp)
  ld s4, 40(sp)
  ld s5, 48(sp)
  ld s6, 56(sp)
  addi sp, sp, 64
  ret
