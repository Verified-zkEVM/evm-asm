/-
  EvmAsm.Codegen.Programs.Bls12MapG2Real

  Extracted from `Bls12Map.lean` to keep every file under the
  `FileSizeGuard` line cap. Holds the real BLS12-381 map-Fp2-to-G2
  (0x11) kernel string (pure assembly text); assembled back into the
  map-precompile suite via `bls12MapKernelFunctions` in `Bls12Map.lean`.
-/

namespace EvmAsm.Codegen

/-- Real BLS12-381 map-Fp2-to-G2 (0x11) kernel: a0 = raw 128-byte wire
    Fp2 element (two padded felts c0 || c1), a1 = 192-byte compact BE
    G2 output. py_ecc optimized_swu_G2 + iso_map_G2 + clear_cofactor
    (h_eff_G2 scalar mul via the affine blsg2 ops). a0 = 0 ok / 1 bad. -/
def zkvmBls12MapFp2ToG2RealFunction : String :=
  ".globl zkvm_bls12_map_fp2_to_g2\n" ++
  "zkvm_bls12_map_fp2_to_g2:\n" ++
  "  addi sp, sp, -48
  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)
  mv s0, a0; mv s1, a1
  addi a0, s0, 0
  li a1, 16
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_invalid
  addi a0, s0, 16
  jal ra, blsg_lt_p
  beqz a0, .Lblm2_invalid
  addi a0, s0, 16
  la a1, blm2_t
  jal ra, blsg_be_to_le
  addi a0, s0, 64
  li a1, 16
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_invalid
  addi a0, s0, 80
  jal ra, blsg_lt_p
  beqz a0, .Lblm2_invalid
  addi a0, s0, 80
  la a1, blm2_t
  addi a1, a1, 48
  jal ra, blsg_be_to_le
  la a0, blm2_t
  li a1, 48
  jal ra, blsg_is_zero_n
  la t0, blm2_t
  ld t1, 0(t0)
  andi t1, t1, 1
  ld t2, 48(t0)
  andi t2, t2, 1
  and t2, t2, a0
  or s4, t1, t2                  # s4 = sgn0(t)
  la a0, blm2_t
  la a1, blm2_t2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_t2
  la a1, blm2_t
  jal ra, blsg2_fp2_mul
  la a0, blm_iso3_z
  la a1, blm2_zt2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_zt2
  la a1, blm2_t2
  jal ra, blsg2_fp2_mul
  la a0, blm2_zt2
  la a1, blm2_tmp
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_tmp
  la a1, blm2_zt2
  jal ra, blsg2_fp2_mul
  la a0, blm2_tmp
  la a1, blm2_zt2
  jal ra, blsg2_fp2_add
  la a0, blm_iso3_a
  la a1, blm2_d
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_d
  la a1, blm2_tmp
  jal ra, blsg2_fp2_mul
  la a0, blm2_d
  la a1, blsg2_pm1_le
  la a2, blm2_d
  jal ra, blsg2_fp_mul
  la a0, blm2_d
  addi a0, a0, 48
  mv t6, a0
  la a1, blsg2_pm1_le
  mv a2, t6
  jal ra, blsg2_fp_mul
  la a0, blm2_tmp
  la a1, blsf_le_one
  la a2, blm2_tmp
  jal ra, blsg2_fp_add
  la a0, blm_iso3_b
  la a1, blm2_n
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_n
  la a1, blm2_tmp
  jal ra, blsg2_fp2_mul
  la a0, blm2_d
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_d_ok
  la a0, blm_iso3_z
  la a1, blm2_d
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_d
  la a1, blm_iso3_a
  jal ra, blsg2_fp2_mul
" ++
  ".Lblm2_d_ok:\n" ++
  "  la a0, blm2_d
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_v
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_v
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm2_n
  la a1, blm2_u
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_u
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_u
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm_iso3_a
  la a1, blm2_w
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_w
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_w
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_u
  la a1, blm2_w
  jal ra, blsg2_fp2_add
  la a0, blm_iso3_b
  la a1, blm2_w
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_w
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_u
  la a1, blm2_w
  jal ra, blsg2_fp2_add
  la a0, blm2_v
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_s2
  la a1, blm2_w
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_w
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_w
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_u
  la a1, blm2_cand
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_cand
  la a1, blm2_w
  jal ra, blsg2_fp2_mul
  la a0, blm2_w
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_cand
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_w
  jal ra, blsg2_fp2_mul
  la a0, blm2_g
  la a1, blm2_s2
  la a2, blm_pm9d16
  li a3, 757
  jal ra, blm_fp2_pow
  la a0, blm2_g
  la a1, blm2_cand
  jal ra, blsg2_fp2_mul
  la a0, blm2_g
  la a1, blm2_r
  li a2, 12
  jal ra, blsf_copy_quads
  li s2, 0                       # success
  la a0, blm_root8_0
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_g
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_u
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_r8_0
  bnez s2, .Lblm2_r8_0
  li s2, 1
  la a0, blm2_s1
  la a1, blm2_r
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_r8_0:\n" ++
  "  la a0, blm_root8_1
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_g
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_u
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_r8_1
  bnez s2, .Lblm2_r8_1
  li s2, 1
  la a0, blm2_s1
  la a1, blm2_r
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_r8_1:\n" ++
  "  la a0, blm_root8_2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_g
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_u
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_r8_2
  bnez s2, .Lblm2_r8_2
  li s2, 1
  la a0, blm2_s1
  la a1, blm2_r
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_r8_2:\n" ++
  "  la a0, blm_root8_3
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_g
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_u
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_r8_3
  bnez s2, .Lblm2_r8_3
  li s2, 1
  la a0, blm2_s1
  la a1, blm2_r
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_r8_3:\n" ++
  "  la a0, blm2_t2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_t
  jal ra, blsg2_fp2_mul
  la a0, blm2_r
  la a1, blm2_cand
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_cand
  la a1, blm2_s1
  jal ra, blsg2_fp2_mul
  la a0, blm2_zt2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm2_zt2
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_zt2
  jal ra, blsg2_fp2_mul
  la a0, blm2_s1
  la a1, blm2_u
  jal ra, blsg2_fp2_mul
  li s3, 0                       # success_2
  la a0, blm2_r
  la a1, blm2_y
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm_eta_0
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_cand
  jal ra, blsg2_fp2_mul
  la a0, blm2_s2
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s2
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_eta_0
  bnez s2, .Lblm2_eta_0
  bnez s3, .Lblm2_eta_0
  li s3, 1
  la a0, blm2_s2
  la a1, blm2_y
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_eta_0:\n" ++
  "  la a0, blm_eta_1
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_cand
  jal ra, blsg2_fp2_mul
  la a0, blm2_s2
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s2
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_eta_1
  bnez s2, .Lblm2_eta_1
  bnez s3, .Lblm2_eta_1
  li s3, 1
  la a0, blm2_s2
  la a1, blm2_y
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_eta_1:\n" ++
  "  la a0, blm_eta_2
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_cand
  jal ra, blsg2_fp2_mul
  la a0, blm2_s2
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s2
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_eta_2
  bnez s2, .Lblm2_eta_2
  bnez s3, .Lblm2_eta_2
  li s3, 1
  la a0, blm2_s2
  la a1, blm2_y
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_eta_2:\n" ++
  "  la a0, blm_eta_3
  la a1, blm2_s2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s2
  la a1, blm2_cand
  jal ra, blsg2_fp2_mul
  la a0, blm2_s2
  la a1, blm2_chk
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_chk
  la a1, blm2_s2
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_v
  jal ra, blsg2_fp2_mul
  la a0, blm2_chk
  la a1, blm2_s1
  jal ra, blsg2_fp2_sub
  la a0, blm2_chk
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_eta_3
  bnez s2, .Lblm2_eta_3
  bnez s3, .Lblm2_eta_3
  li s3, 1
  la a0, blm2_s2
  la a1, blm2_y
  li a2, 12
  jal ra, blsf_copy_quads
" ++
  ".Lblm2_eta_3:\n" ++
  "  or t0, s2, s3
  beqz t0, .Lblm2_invalid        # unreachable per RFC 9380
  bnez s2, .Lblm2_n_ok
  la a0, blm2_n
  la a1, blm2_zt2
  jal ra, blsg2_fp2_mul
" ++
  ".Lblm2_n_ok:\n" ++
  "  la a0, blm2_y
  li a1, 48
  jal ra, blsg_is_zero_n
  la t0, blm2_y
  ld t1, 0(t0)
  andi t1, t1, 1
  ld t2, 48(t0)
  andi t2, t2, 1
  and t2, t2, a0
  or t1, t1, t2
  beq t1, s4, .Lblm2_sgn_ok
  la a0, blm2_y
  la a1, blsg2_pm1_le
  la a2, blm2_y
  jal ra, blsg2_fp_mul
  la a0, blm2_y
  addi a0, a0, 48
  mv t6, a0
  la a1, blsg2_pm1_le
  mv a2, t6
  jal ra, blsg2_fp_mul
" ++
  ".Lblm2_sgn_ok:\n" ++
  "  la a0, blm2_y
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm2_d
  la a1, blm2_zp1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_zp1
  la a1, blm2_zp2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_zp2
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp2
  la a1, blm2_zp3
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_zp3
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm_k3_0_3
  la a1, blm2_m0
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_m0
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp1
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_0_2
  jal ra, blsg2_fp2_mul
  la a0, blm2_m0
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m0
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_0_1
  jal ra, blsg2_fp2_mul
  la a0, blm2_m0
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m0
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp3
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_0_0
  jal ra, blsg2_fp2_mul
  la a0, blm2_m0
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm_k3_1_3
  la a1, blm2_m1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_m1
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp1
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_1_2
  jal ra, blsg2_fp2_mul
  la a0, blm2_m1
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m1
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_1_1
  jal ra, blsg2_fp2_mul
  la a0, blm2_m1
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m1
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp3
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_1_0
  jal ra, blsg2_fp2_mul
  la a0, blm2_m1
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm_k3_2_3
  la a1, blm2_m2
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_m2
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp1
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_2_2
  jal ra, blsg2_fp2_mul
  la a0, blm2_m2
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m2
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_2_1
  jal ra, blsg2_fp2_mul
  la a0, blm2_m2
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m2
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp3
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_2_0
  jal ra, blsg2_fp2_mul
  la a0, blm2_m2
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm_k3_3_3
  la a1, blm2_m3
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_m3
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp1
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_3_2
  jal ra, blsg2_fp2_mul
  la a0, blm2_m3
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m3
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp2
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_3_1
  jal ra, blsg2_fp2_mul
  la a0, blm2_m3
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m3
  la a1, blm2_n
  jal ra, blsg2_fp2_mul
  la a0, blm2_zp3
  la a1, blm2_s1
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_s1
  la a1, blm_k3_3_0
  jal ra, blsg2_fp2_mul
  la a0, blm2_m3
  la a1, blm2_s1
  jal ra, blsg2_fp2_add
  la a0, blm2_m2
  la a1, blm2_y
  jal ra, blsg2_fp2_mul
  la a0, blm2_m3
  la a1, blm2_d
  jal ra, blsg2_fp2_mul
  la a0, blm2_m1
  la a1, blm2_zg
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_zg
  la a1, blm2_m3
  jal ra, blsg2_fp2_mul
  la a0, blm2_m0
  la a1, blm2_xg
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_xg
  la a1, blm2_m3
  jal ra, blsg2_fp2_mul
  la a0, blm2_m1
  la a1, blm2_yg
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_yg
  la a1, blm2_m2
  jal ra, blsg2_fp2_mul
  la a0, blm2_zg
  li a1, 96
  jal ra, blsg_is_zero_n
  beqz a0, .Lblm2_fin
  mv a0, s1
  jal ra, blsg2_zero192          # infinity output
  j .Lblm2_ok
" ++
  ".Lblm2_fin:\n" ++
  "  la a0, blm2_zg
  la a1, blm2_zinv
  jal ra, blsg2_fp2_inv
  la a0, blm2_xg
  la a1, blm2_zinv
  jal ra, blsg2_fp2_mul
  la a0, blm2_yg
  la a1, blm2_zinv
  jal ra, blsg2_fp2_mul
  la a0, blm2_xg
  la a1, blm2_aff
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm2_yg
  la a1, blm2_aff
  addi a1, a1, 96
  li a2, 12
  jal ra, blsf_copy_quads
  la a0, blm_heff_g2_be
  li a1, 80
  la a2, blm2_aff
  la a3, blm2_res
  jal ra, blsg2_scalar_mul
  la a0, blm2_res
  mv a1, s1
  jal ra, blsg2_encode
" ++
  ".Lblm2_ok:\n" ++
  "  li a0, 0\n" ++
  "  j .Lblm2_ret\n" ++
  ".Lblm2_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblm2_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

end EvmAsm.Codegen
