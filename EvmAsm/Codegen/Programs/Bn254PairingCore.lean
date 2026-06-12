/-
  EvmAsm.Codegen.Programs.Bn254PairingCore

  The alt_bn128 ecPairing (0x08) kernel, bead
  evm-asm-fhsxz.2.4.2.62.10.1 layers 3b/4: G2 (FQ2) projective
  arithmetic for the EIP-197 subgroup check, the py_ecc-mirroring
  Miller loop over FQ12, and `zkvm_bn254_pairing`.

  Algorithm = execution-specs `alt_bn128_pairing_check`, which computes
  ∏ pairing(Q_i, P_i) with py_ecc `optimized_bn128`. Two semantically
  exact rewrites keep the step count down:

    * the per-pair division f_num/f_den and the per-pair final
      exponentiation are hoisted: numerators and denominators multiply
      across pairs and ONE Fermat inverse (x^(p^12 - 2)) plus ONE final
      exponentiation (x^((p^12-1)/n)) run at the end —
      ∏ (fn_i/fd_i)^E = ((∏ fn_i)·(∏ fd_i)^-1)^E;
    * the G1 subgroup check is_inf(n·P) always passes for a validated
      G1 point (the curve has cofactor 1), so it is not recomputed.

  The G2 subgroup check is real (the twist has a large cofactor):
  is_inf(n·Q) via FQ2 projective double-and-add. Kernel ABI:

    zkvm_bn254_pairing(a0 = input bytes (BE, 192·k), a1 = k,
                       a2 = result byte ptr)
      -> a0 = 0 ok (result byte = 1 iff the product is one),
         a0 = 1 invalid input (coord >= p, off-curve, or Q outside the
         subgroup) — the spec's OutOfGasError precompile failure.

  Depends on the bnf_/bnc_ BE suites (`Bn254Field`/`Bn254Curve`) for
  input validation, the bnp_ Fp2 layer, and the bnq_ FQ12 machine.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Bn254Curve
import EvmAsm.Codegen.Programs.Bn254Fq12Point

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Pairing-core data labels WITHOUT a `.section .data` header. -/
def bn254PairingDataFragment : String :=
  ".balign 8\n" ++
  -- py_ecc pseudo_binary_encoding[63::-1] (the Miller iteration order);
  -- 2 encodes -1.
  "bnq_pbe:\n" ++
  "  .byte 1,0,1,0,0,2,0,1,1,0,0,0,2,0,0,1\n" ++
  "  .byte 1,0,0,2,0,0,0,0,0,1,0,0,2,0,0,1\n" ++
  "  .byte 1,1,0,0,0,0,2,0,1,0,0,2,0,1,1,0\n" ++
  "  .byte 0,1,0,0,2,1,0,0,2,0,1,0,1,0,0,0\n" ++
  -- FQ12 projective working points (X||Y||Z, 384 B each).
  ".balign 8\n" ++
  "bnq_R:\n  .zero 1152\n" ++
  "bnq_Q:\n  .zero 1152\n" ++
  "bnq_Qa:\n  .zero 1152\n" ++
  "bnq_P:\n  .zero 1152\n" ++
  -- Line outputs, per-pair miller accumulators, cross-pair accumulators,
  -- and a multiply temporary.
  "bnq_ln:\n  .zero 384\n" ++
  "bnq_ld:\n  .zero 384\n" ++
  "bnq_fn:\n  .zero 384\n" ++
  "bnq_fd:\n  .zero 384\n" ++
  "bnq_tn:\n  .zero 384\n" ++
  "bnq_td:\n  .zero 384\n" ++
  "bnq_m0:\n  .zero 384\n" ++
  -- G2 affine input (FQ2 LE), the projective subgroup-check registers,
  -- the FQ2 temp pool, and the G1 LE coordinates.
  ".balign 8\n" ++
  "bng_qx:\n  .zero 64\n" ++
  "bng_qy:\n  .zero 64\n" ++
  "bng_B:\n  .zero 192\n" ++
  "bng_R:\n  .zero 192\n" ++
  "bng_t0:\n  .zero 64\n" ++
  "bng_t1:\n  .zero 64\n" ++
  "bng_t2:\n  .zero 64\n" ++
  "bng_t3:\n  .zero 64\n" ++
  "bng_t4:\n  .zero 64\n" ++
  "bng_t5:\n  .zero 64\n" ++
  "bng_t6:\n  .zero 64\n" ++
  "bng_t7:\n  .zero 64\n" ++
  "bng_t8:\n  .zero 64\n" ++
  "bng_t9:\n  .zero 64\n" ++
  "bng_px:\n  .zero 32\n" ++
  "bng_py:\n  .zero 32\n"

private def fp2c (src dst : String) : String :=
  "  la a0, " ++ src ++ "\n" ++
  "  la a1, " ++ dst ++ "\n" ++
  "  jal ra, bnp_fp2_copy\n"

private def fp2op (fn dst src : String) : String :=
  "  la a0, " ++ dst ++ "\n" ++
  "  la a1, " ++ src ++ "\n" ++
  "  jal ra, bnp_" ++ fn ++ "\n"

/-- Double an FQ2 projective point (same formulas as `bnq_pt_double`,
    over the accelerator-backed Fp2 layer). a0 = dst (192 B X||Y||Z),
    a1 = src; dst may alias src. -/
def bn254G2DoubleFunction : String :=
  "bng2_double:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  -- t0 = x^2 ; t1 = W = 3 x^2
  "  mv a0, s1\n  la a1, bng_t0\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t0\n  mv a1, s1\n  jal ra, bnp_fp2_mul\n" ++
  fp2c "bng_t0" "bng_t1" ++
  fp2op "fp2_add" "bng_t1" "bng_t0" ++
  fp2op "fp2_add" "bng_t1" "bng_t0" ++
  -- t2 = S = y z
  "  addi a0, s1, 64\n  la a1, bng_t2\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t2\n  addi a1, s1, 128\n  jal ra, bnp_fp2_mul\n" ++
  -- t3 = B = x y S
  "  mv a0, s1\n  la a1, bng_t3\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t3\n  addi a1, s1, 64\n  jal ra, bnp_fp2_mul\n" ++
  fp2op "fp2_mul" "bng_t3" "bng_t2" ++
  -- t4 = H = W^2 - 8B
  fp2c "bng_t1" "bng_t4" ++
  fp2op "fp2_mul" "bng_t4" "bng_t1" ++
  fp2c "bng_t3" "bng_t5" ++
  fp2op "fp2_add" "bng_t5" "bng_t5" ++
  fp2op "fp2_add" "bng_t5" "bng_t5" ++
  fp2op "fp2_add" "bng_t5" "bng_t5" ++
  fp2op "fp2_sub" "bng_t4" "bng_t5" ++
  -- t5 = X' = 2 H S
  fp2c "bng_t4" "bng_t5" ++
  fp2op "fp2_mul" "bng_t5" "bng_t2" ++
  fp2op "fp2_add" "bng_t5" "bng_t5" ++
  -- t6 = S^2
  fp2c "bng_t2" "bng_t6" ++
  fp2op "fp2_mul" "bng_t6" "bng_t2" ++
  -- t7 = Y' = W (4B - H) - 8 y^2 S^2
  fp2c "bng_t3" "bng_t7" ++
  fp2op "fp2_add" "bng_t7" "bng_t7" ++
  fp2op "fp2_add" "bng_t7" "bng_t7" ++
  fp2op "fp2_sub" "bng_t7" "bng_t4" ++
  fp2op "fp2_mul" "bng_t7" "bng_t1" ++
  "  addi a0, s1, 64\n  la a1, bng_t8\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t8\n  addi a1, s1, 64\n  jal ra, bnp_fp2_mul\n" ++
  fp2op "fp2_mul" "bng_t8" "bng_t6" ++
  fp2op "fp2_add" "bng_t8" "bng_t8" ++
  fp2op "fp2_add" "bng_t8" "bng_t8" ++
  fp2op "fp2_add" "bng_t8" "bng_t8" ++
  fp2op "fp2_sub" "bng_t7" "bng_t8" ++
  -- t6 = Z' = 8 S^3
  fp2op "fp2_mul" "bng_t6" "bng_t2" ++
  fp2op "fp2_add" "bng_t6" "bng_t6" ++
  fp2op "fp2_add" "bng_t6" "bng_t6" ++
  fp2op "fp2_add" "bng_t6" "bng_t6" ++
  "  la a0, bng_t5\n  mv a1, s0\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t7\n  addi a1, s0, 64\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t6\n  addi a1, s0, 128\n  jal ra, bnp_fp2_copy\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Add two FQ2 projective points (py_ecc `add` over Fp2).
    a0 = dst, a1 = p1, a2 = p2; dst may alias p1/p2. -/
def bn254G2AddFunction : String :=
  "bng2_add:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  addi a0, s1, 128\n" ++
  "  jal ra, bnp_fp2_is_zero\n" ++
  "  beqz a0, .Lbng2_add_p1fin\n" ++
  "  mv t5, s2\n" ++
  "  j .Lbng2_add_copy_in\n" ++
  ".Lbng2_add_p1fin:\n" ++
  "  addi a0, s2, 128\n" ++
  "  jal ra, bnp_fp2_is_zero\n" ++
  "  beqz a0, .Lbng2_add_p2fin\n" ++
  "  mv t5, s1\n" ++
  ".Lbng2_add_copy_in:\n" ++
  "  li t2, 24\n" ++
  "  mv t3, s0\n" ++
  ".Lbng2_add_copy_loop:\n" ++
  "  ld t4, 0(t5)\n" ++
  "  sd t4, 0(t3)\n" ++
  "  addi t5, t5, 8\n" ++
  "  addi t3, t3, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbng2_add_copy_loop\n" ++
  "  j .Lbng2_add_ret\n" ++
  ".Lbng2_add_p2fin:\n" ++
  -- t0 = U1 = y2 z1 ; t1 = U2 = y1 z2 ; t2 = V1 = x2 z1 ; t3 = V2 = x1 z2
  "  addi a0, s2, 64\n  la a1, bng_t0\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t0\n  addi a1, s1, 128\n  jal ra, bnp_fp2_mul\n" ++
  "  addi a0, s1, 64\n  la a1, bng_t1\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t1\n  addi a1, s2, 128\n  jal ra, bnp_fp2_mul\n" ++
  "  mv a0, s2\n  la a1, bng_t2\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t2\n  addi a1, s1, 128\n  jal ra, bnp_fp2_mul\n" ++
  "  mv a0, s1\n  la a1, bng_t3\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t3\n  addi a1, s2, 128\n  jal ra, bnp_fp2_mul\n" ++
  "  la a0, bng_t2\n" ++
  "  la a1, bng_t3\n" ++
  "  jal ra, bnp_fp2_eq\n" ++
  "  beqz a0, .Lbng2_add_general\n" ++
  "  la a0, bng_t0\n" ++
  "  la a1, bng_t1\n" ++
  "  jal ra, bnp_fp2_eq\n" ++
  "  beqz a0, .Lbng2_add_inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bng2_double\n" ++
  "  j .Lbng2_add_ret\n" ++
  ".Lbng2_add_inf:\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, bnp_fp2_zero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s0)                   # x = one\n" ++
  "  addi a0, s0, 64\n" ++
  "  jal ra, bnp_fp2_zero\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 64(s0)                  # y = one\n" ++
  "  addi a0, s0, 128\n" ++
  "  jal ra, bnp_fp2_zero           # z = zero\n" ++
  "  j .Lbng2_add_ret\n" ++
  ".Lbng2_add_general:\n" ++
  -- t4 = U = U1 - U2 ; t5 = V = V1 - V2
  fp2c "bng_t0" "bng_t4" ++
  fp2op "fp2_sub" "bng_t4" "bng_t1" ++
  fp2c "bng_t2" "bng_t5" ++
  fp2op "fp2_sub" "bng_t5" "bng_t3" ++
  -- t6 = V^2 ; t7 = V^2 V2 ; t6 = V^3
  fp2c "bng_t5" "bng_t6" ++
  fp2op "fp2_mul" "bng_t6" "bng_t5" ++
  fp2c "bng_t6" "bng_t7" ++
  fp2op "fp2_mul" "bng_t7" "bng_t3" ++
  fp2op "fp2_mul" "bng_t6" "bng_t5" ++
  -- t8 = W = z1 z2
  "  addi a0, s1, 128\n  la a1, bng_t8\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t8\n  addi a1, s2, 128\n  jal ra, bnp_fp2_mul\n" ++
  -- t9 = A = U^2 W - V^3 - 2 V^2 V2
  fp2c "bng_t4" "bng_t9" ++
  fp2op "fp2_mul" "bng_t9" "bng_t4" ++
  fp2op "fp2_mul" "bng_t9" "bng_t8" ++
  fp2op "fp2_sub" "bng_t9" "bng_t6" ++
  fp2c "bng_t7" "bng_t0" ++
  fp2op "fp2_add" "bng_t0" "bng_t0" ++
  fp2op "fp2_sub" "bng_t9" "bng_t0" ++
  -- t5 = X' = V A
  fp2op "fp2_mul" "bng_t5" "bng_t9" ++
  -- t7 = Y' = U (V^2 V2 - A) - V^3 U2
  fp2op "fp2_sub" "bng_t7" "bng_t9" ++
  fp2op "fp2_mul" "bng_t7" "bng_t4" ++
  fp2c "bng_t6" "bng_t0" ++
  fp2op "fp2_mul" "bng_t0" "bng_t1" ++
  fp2op "fp2_sub" "bng_t7" "bng_t0" ++
  -- t6 = Z' = V^3 W
  fp2op "fp2_mul" "bng_t6" "bng_t8" ++
  "  la a0, bng_t5\n  mv a1, s0\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t7\n  addi a1, s0, 64\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t6\n  addi a1, s0, 128\n  jal ra, bnp_fp2_copy\n" ++
  ".Lbng2_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- EIP-197 G2 subgroup check: a0 = 1 iff n·Q is the identity, where Q
    is the affine FQ2 point staged in `bng_qx`/`bng_qy` (finite). MSB-
    first double-and-add over `bnq_order_le` bits 253..0. -/
def bn254G2SubgroupCheckFunction : String :=
  "bng2_subgroup_ok:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s3, 8(sp)\n" ++
  fp2c "bng_qx" "bng_B" ++
  "  la a0, bng_qy\n  la a1, bng_B\n  addi a1, a1, 64\n  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_B\n" ++
  "  addi a0, a0, 128\n" ++
  "  jal ra, bnp_fp2_zero\n" ++
  "  la t0, bng_B\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 128(t0)                 # z = one\n" ++
  "  la a0, bng_R\n" ++
  "  jal ra, bnp_fp2_zero\n" ++
  "  la a0, bng_R\n  addi a0, a0, 64\n  jal ra, bnp_fp2_zero\n" ++
  "  la a0, bng_R\n  addi a0, a0, 128\n  jal ra, bnp_fp2_zero\n" ++
  "  la t0, bng_R\n" ++
  "  li t1, 1\n" ++
  "  sd t1, 0(t0)\n" ++
  "  sd t1, 64(t0)                  # R = (one, one, zero)\n" ++
  "  li s3, 253\n" ++
  ".Lbng2_sg_loop:\n" ++
  "  la a0, bng_R\n" ++
  "  la a1, bng_R\n" ++
  "  jal ra, bng2_double\n" ++
  "  la t0, bnq_order_le\n" ++
  "  srli t1, s3, 6\n" ++
  "  slli t1, t1, 3\n" ++
  "  add t0, t0, t1\n" ++
  "  ld t1, 0(t0)\n" ++
  "  andi t2, s3, 63\n" ++
  "  srl t1, t1, t2\n" ++
  "  andi t1, t1, 1\n" ++
  "  beqz t1, .Lbng2_sg_skip\n" ++
  "  la a0, bng_R\n" ++
  "  la a1, bng_R\n" ++
  "  la a2, bng_B\n" ++
  "  jal ra, bng2_add\n" ++
  ".Lbng2_sg_skip:\n" ++
  "  beqz s3, .Lbng2_sg_done\n" ++
  "  addi s3, s3, -1\n" ++
  "  j .Lbng2_sg_loop\n" ++
  ".Lbng2_sg_done:\n" ++
  "  la a0, bng_R\n" ++
  "  addi a0, a0, 128\n" ++
  "  jal ra, bnp_fp2_is_zero\n" ++
  "  ld ra, 0(sp); ld s3, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

def bn254G2CommonFunctions : String :=
  bn254G2DoubleFunction ++ "\n" ++
  bn254G2AddFunction ++ "\n" ++
  bn254G2SubgroupCheckFunction

end EvmAsm.Codegen
