ssz_merkleize:
  addi sp, sp, -64
  sd ra,  0(sp)
  sd s0,  8(sp)
  sd s1, 16(sp)
  sd s2, 24(sp)
  sd s3, 32(sp)
  sd s4, 40(sp)
  sd s5, 48(sp)
  sd s6, 56(sp)
  # s5 = chunks_in ptr; s0 = n; s1 = limit_log2 L; s6 = out ptr
  mv s5, a0
  mv s0, a1
  mv s1, a2
  mv s6, a3
  # n == 0 → root is Z_L (look up directly)
  beqz s0, .Lszm_zero_path
  # phase 1: compute M = next_pow2(n) and depth_M = log2(M)
  li t0, 1                    # candidate M
  li s4, 0                    # candidate depth
.Lszm_pow2_scan:
  bge t0, s0, .Lszm_have_M
  slli t0, t0, 1
  addi s4, s4, 1
  j .Lszm_pow2_scan
.Lszm_have_M:
  mv s3, t0                   # s3 = M; s4 = depth_M = log2(M)
  # copy n*32 input bytes into ssz_merkleize_padded, zero-pad the rest
  la t0, ssz_merkleize_padded
  slli t1, s0, 5              # t1 = n*32 bytes to copy
  mv t2, s5                   # src
  mv t3, t0                   # dst
.Lszm_cp:
  beqz t1, .Lszm_pad
  ld t4, 0(t2)
  sd t4, 0(t3)
  addi t2, t2, 8
  addi t3, t3, 8
  addi t1, t1, -8
  j .Lszm_cp
.Lszm_pad:
  sub t1, s3, s0              # t1 = M - n (slots to zero)
  slli t1, t1, 5              # t1 = (M-n)*32 bytes
.Lszm_zr:
  beqz t1, .Lszm_call_pow2
  sd zero, 0(t3)
  addi t3, t3, 8
  addi t1, t1, -8
  j .Lszm_zr
.Lszm_call_pow2:
  # call ssz_merkleize_pow2(padded, M, ssz_merkleize_partial)
  la a0, ssz_merkleize_padded
  mv a1, s3
  la a2, ssz_merkleize_partial
  jal ra, ssz_merkleize_pow2
  # phase 2: mix in Z_d for d in [depth_M, L)
.Lszm_mix:
  beq s4, s1, .Lszm_copy_out
  # ssz_merkleize_partial[0..32]   = current root (input L)
  # ssz_merkleize_partial[32..64]  = Z_{s4}        (input R)
  la t0, ssz_zero_hashes
  slli t1, s4, 5              # offset = s4*32
  add t0, t0, t1              # &Z_{s4}
  la t2, ssz_merkleize_partial
  addi t2, t2, 32             # &partial[32..]
  ld t3,  0(t0); sd t3,  0(t2)
  ld t3,  8(t0); sd t3,  8(t2)
  ld t3, 16(t0); sd t3, 16(t2)
  ld t3, 24(t0); sd t3, 24(t2)
  la a0, ssz_merkleize_partial
  li a1, 64
  la a2, ssz_merkleize_partial
  jal ra, zkvm_sha256
  addi s4, s4, 1
  j .Lszm_mix
.Lszm_copy_out:
  la t0, ssz_merkleize_partial
  ld t1,  0(t0); sd t1,  0(s6)
  ld t1,  8(t0); sd t1,  8(s6)
  ld t1, 16(t0); sd t1, 16(s6)
  ld t1, 24(t0); sd t1, 24(s6)
  j .Lszm_ret
.Lszm_zero_path:
  # root = Z_L (n == 0 case)
  la t0, ssz_zero_hashes
  slli t1, s1, 5
  add t0, t0, t1
  ld t1,  0(t0); sd t1,  0(s6)
  ld t1,  8(t0); sd t1,  8(s6)
  ld t1, 16(t0); sd t1, 16(s6)
  ld t1, 24(t0); sd t1, 24(s6)
.Lszm_ret:
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
