/-
  EvmAsm.Codegen.Programs.Bn254Pairing

  The alt_bn128 ecPairing (0x08) Miller loop and `zkvm_bn254_pairing`
  kernel (bead evm-asm-fhsxz.2.4.2.62.10.1 layer 4). See
  `Bn254PairingCore.lean` for the algorithm provenance (py_ecc
  optimized_bn128, as called by execution-specs) and the two exact
  hoisting rewrites (cross-pair num/den accumulation, single final
  exponentiation).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.Bn254PairingCore

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def q12 (fn d a b : String) : String :=
  "  la a0, " ++ d ++ "\n" ++
  "  la a1, " ++ a ++ "\n" ++
  "  la a2, " ++ b ++ "\n" ++
  "  jal ra, " ++ fn ++ "\n"

/-- Copy a 1152-byte FQ12 projective point: a0 = src, a1 = dst. -/
def bnqPtCopy_prog : Program :=
  [ .LI .x7 (144 : Word),
    .LD .x28 .x10 (0 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254PtCopyFunction : String :=
  "bnq_pt_copy:\n" ++ emitProgram bnqPtCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnqPtCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254PtCopyFunction_eq_prog :
    bn254PtCopyFunction = "bnq_pt_copy:\n" ++ emitProgram bnqPtCopy_prog := rfl

#guard bn254PtCopyFunction.startsWith "bnq_pt_copy:\n"
/-- py_ecc `miller_loop(Q, P, final_exponentiate=False)` accumulated as
    a fraction: multiplies `bnq_tn` by f_num and `bnq_td` by f_den.
    Expects the twisted Q in `bnq_Q` and the cast P in `bnq_P` (both
    finite, Z = one). Clobbers bnq_R/bnq_Qa/bnq_ln/bnq_ld/bnq_fn/
    bnq_fd/bnq_m0 and the bnq_d pool. -/
def bn254MillerFunction : String :=
  "bnq_miller_accumulate:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s3, 8(sp); sd s4, 16(sp)\n" ++
  -- R = Q ; f_num = f_den = one ; Qa = neg(Q) = (x, -y, z)
  "  la a0, bnq_Q\n" ++
  "  la a1, bnq_R\n" ++
  "  jal ra, bnq_pt_copy\n" ++
  "  la a0, bnq_fn\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  la a0, bnq_fd\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  la a0, bnq_Q\n" ++
  "  la a1, bnq_Qa\n" ++
  "  jal ra, bnq_pt_copy\n" ++
  "  la a0, bnq_Qa\n" ++
  "  addi a0, a0, 384\n" ++
  "  la a1, bnq_Q\n" ++
  "  addi a1, a1, 384\n" ++
  "  la a2, bnp_p_minus_1_le\n" ++
  "  jal ra, bnq_smul               # Qa.y = -Q.y\n" ++
  "  li s3, 0                       # iteration index\n" ++
  ".Lbnq_ml_loop:\n" ++
  -- doubling step: f = f^2 * line(R, R, P) ; R = 2R
  "  la a0, bnq_ln\n" ++
  "  la a1, bnq_ld\n" ++
  "  la a2, bnq_R\n" ++
  "  la a3, bnq_R\n" ++
  "  la a4, bnq_P\n" ++
  "  jal ra, bnq_linefunc\n" ++
  q12 "bnq_mul" "bnq_m0" "bnq_fn" "bnq_fn" ++
  q12 "bnq_mul" "bnq_fn" "bnq_m0" "bnq_ln" ++
  q12 "bnq_mul" "bnq_m0" "bnq_fd" "bnq_fd" ++
  q12 "bnq_mul" "bnq_fd" "bnq_m0" "bnq_ld" ++
  "  la a0, bnq_R\n" ++
  "  la a1, bnq_R\n" ++
  "  jal ra, bnq_pt_double\n" ++
  "  la t0, bnq_pbe\n" ++
  "  add t0, t0, s3\n" ++
  "  lbu s4, 0(t0)\n" ++
  "  beqz s4, .Lbnq_ml_next\n" ++
  "  la t0, bnq_Q\n" ++
  "  li t1, 1\n" ++
  "  beq s4, t1, .Lbnq_ml_have_a\n" ++
  "  la t0, bnq_Qa\n" ++
  ".Lbnq_ml_have_a:\n" ++
  "  mv s4, t0                      # A = Q or neg(Q)\n" ++
  "  la a0, bnq_ln\n" ++
  "  la a1, bnq_ld\n" ++
  "  la a2, bnq_R\n" ++
  "  mv a3, s4\n" ++
  "  la a4, bnq_P\n" ++
  "  jal ra, bnq_linefunc\n" ++
  q12 "bnq_mul" "bnq_fn" "bnq_fn" "bnq_ln" ++
  q12 "bnq_mul" "bnq_fd" "bnq_fd" "bnq_ld" ++
  "  la a0, bnq_R\n" ++
  "  la a1, bnq_R\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, bnq_pt_add\n" ++
  ".Lbnq_ml_next:\n" ++
  "  addi s3, s3, 1\n" ++
  "  li t0, 64\n" ++
  "  bne s3, t0, .Lbnq_ml_loop\n" ++
  -- Q1 = (Q.x^p, Q.y^p, Q.z^p) into Qa
  "  la a0, bnq_Qa\n" ++
  "  la a1, bnq_Q\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_Qa\n" ++
  "  addi a0, a0, 384\n" ++
  "  la a1, bnq_Q\n" ++
  "  addi a1, a1, 384\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_Qa\n" ++
  "  addi a0, a0, 768\n" ++
  "  la a1, bnq_Q\n" ++
  "  addi a1, a1, 768\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_ln\n" ++
  "  la a1, bnq_ld\n" ++
  "  la a2, bnq_R\n" ++
  "  la a3, bnq_Qa\n" ++
  "  la a4, bnq_P\n" ++
  "  jal ra, bnq_linefunc\n" ++
  q12 "bnq_mul" "bnq_fn" "bnq_fn" "bnq_ln" ++
  q12 "bnq_mul" "bnq_fd" "bnq_fd" "bnq_ld" ++
  q12 "bnq_pt_add" "bnq_R" "bnq_R" "bnq_Qa" ++
  -- nQ2 = (Q1.x^p, -(Q1.y^p), Q1.z^p) in place (pow dst != base via m0)
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_Qa\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_Qa\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_Qa\n" ++
  "  addi a1, a1, 384\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_Qa\n" ++
  "  addi a0, a0, 384\n" ++
  "  la a1, bnq_m0\n" ++
  "  la a2, bnp_p_minus_1_le\n" ++
  "  jal ra, bnq_smul\n" ++
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_Qa\n" ++
  "  addi a1, a1, 768\n" ++
  "  la a2, bnq_exp_p_le\n" ++
  "  li a3, 253\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_Qa\n" ++
  "  addi a1, a1, 768\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_ln\n" ++
  "  la a1, bnq_ld\n" ++
  "  la a2, bnq_R\n" ++
  "  la a3, bnq_Qa\n" ++
  "  la a4, bnq_P\n" ++
  "  jal ra, bnq_linefunc\n" ++
  q12 "bnq_mul" "bnq_fn" "bnq_fn" "bnq_ln" ++
  q12 "bnq_mul" "bnq_fd" "bnq_fd" "bnq_ld" ++
  -- accumulate across pairs
  q12 "bnq_mul" "bnq_tn" "bnq_tn" "bnq_fn" ++
  q12 "bnq_mul" "bnq_td" "bnq_td" "bnq_fd" ++
  "  ld ra, 0(sp); ld s3, 8(sp); ld s4, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Real BN254 ecPairing kernel. a0 = input bytes (BE, 192·k), a1 = k,
    a2 = result byte pointer. Returns a0 = 0 (result byte = 1 iff the
    pairing product is one) or a0 = 1 on invalid input (the spec's
    OutOfGasError). -/
def zkvmBn254PairingRealFunction : String :=
  ".globl zkvm_bn254_pairing\n" ++
  "zkvm_bn254_pairing:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la a0, bnq_tn\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  la a0, bnq_td\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  li s3, 0                       # pair index\n" ++
  ".Lbnpair_loop:\n" ++
  "  bgeu s3, s1, .Lbnpair_finish\n" ++
  "  li t0, 192\n" ++
  "  mul t0, t0, s3\n" ++
  "  add s6, s0, t0                 # this pair's base\n" ++
  -- G1: execution-specs bytes_to_g1 (coords < p, on-curve or (0,0)).
  "  mv a0, s6\n" ++
  "  jal ra, bnc_validate_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lbnpair_invalid\n" ++
  "  mv s4, a0                      # 1 = P at infinity\n" ++
  -- G2 coordinate range checks (BE: x_im, x_re, y_im, y_re).
  "  addi a0, s6, 64\n" ++
  "  jal ra, bnf_lt_p\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  "  addi a0, s6, 96\n" ++
  "  jal ra, bnf_lt_p\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  "  addi a0, s6, 128\n" ++
  "  jal ra, bnf_lt_p\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  "  addi a0, s6, 160\n" ++
  "  jal ra, bnf_lt_p\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  -- Stage Q (LE): c0 = real (second word), c1 = imaginary (first word).
  "  addi a0, s6, 96\n" ++
  "  la a1, bng_qx\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  addi a0, s6, 64\n" ++
  "  la a1, bng_qx\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  addi a0, s6, 160\n" ++
  "  la a1, bng_qy\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  addi a0, s6, 128\n" ++
  "  la a1, bng_qy\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  la a0, bng_qx\n" ++
  "  jal ra, bnp_fp2_is_zero\n" ++
  "  mv s5, a0\n" ++
  "  la a0, bng_qy\n" ++
  "  jal ra, bnp_fp2_is_zero\n" ++
  "  and s5, s5, a0                 # 1 = Q at infinity\n" ++
  "  bnez s5, .Lbnpair_q_ok\n" ++
  -- finite Q: on the twist (y^2 = x^3 + b2) and in the order-n subgroup.
  "  la a0, bng_qx\n" ++
  "  la a1, bng_t0\n" ++
  "  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t0\n" ++
  "  la a1, bng_qx\n" ++
  "  jal ra, bnp_fp2_mul\n" ++
  "  la a0, bng_t0\n" ++
  "  la a1, bng_qx\n" ++
  "  jal ra, bnp_fp2_mul            # x^3\n" ++
  "  la a0, bng_t0\n" ++
  "  la a1, bnq_twist_b2_le\n" ++
  "  jal ra, bnp_fp2_add\n" ++
  "  la a0, bng_qy\n" ++
  "  la a1, bng_t1\n" ++
  "  jal ra, bnp_fp2_copy\n" ++
  "  la a0, bng_t1\n" ++
  "  la a1, bng_qy\n" ++
  "  jal ra, bnp_fp2_mul            # y^2\n" ++
  "  la a0, bng_t1\n" ++
  "  la a1, bng_t0\n" ++
  "  jal ra, bnp_fp2_eq\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  "  jal ra, bng2_subgroup_ok\n" ++
  "  beqz a0, .Lbnpair_invalid\n" ++
  ".Lbnpair_q_ok:\n" ++
  -- pairing(Q, P) = one when either is at infinity: skip.
  "  or t0, s4, s5\n" ++
  "  bnez t0, .Lbnpair_next\n" ++
  -- cast P to FQ12 projective: X = (xP, 0...), Y = (yP, 0...), Z = one.
  "  mv a0, s6\n" ++
  "  la a1, bng_px\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  addi a0, s6, 32\n" ++
  "  la a1, bng_py\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  la a0, bnq_P\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la a0, bnq_P\n" ++
  "  addi a0, a0, 384\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la a0, bnq_P\n" ++
  "  addi a0, a0, 768\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la t0, bng_px\n" ++
  "  la t1, bnq_P\n" ++
  "  ld t2, 0(t0);  sd t2, 0(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 8(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 16(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 24(t1)\n" ++
  "  la t0, bng_py\n" ++
  "  ld t2, 0(t0);  sd t2, 384(t1)\n" ++
  "  ld t2, 8(t0);  sd t2, 392(t1)\n" ++
  "  ld t2, 16(t0); sd t2, 400(t1)\n" ++
  "  ld t2, 24(t0); sd t2, 408(t1)\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 768(t1)                 # Z = one\n" ++
  -- twist Q into bnq_Q: X coeffs {2: xc0 - 9 xc1, 8: xc1},
  -- Y coeffs {3: yc0 - 9 yc1, 9: yc1}, Z = one (py_ecc `twist`).
  "  la a0, bnq_Q\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la a0, bnq_Q\n" ++
  "  addi a0, a0, 384\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la a0, bnq_Q\n" ++
  "  addi a0, a0, 768\n" ++
  "  jal ra, bnq_zero\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  la t1, bng_qx\n" ++
  "  addi t2, t1, 32\n" ++
  "  sd t2, 0(t0)                   # a = xc1\n" ++
  "  la t2, bnq_le_pm9\n" ++
  "  sd t2, 8(t0)                   # b = p - 9\n" ++
  "  sd t1, 16(t0)                  # c = xc0\n" ++
  "  la t2, bnf_le_p\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t2, bnq_Q\n" ++
  "  addi t2, t2, 64\n" ++
  "  sd t2, 32(t0)                  # X[2] = xc0 - 9 xc1\n" ++
  "  .4byte 0x8022a073\n" ++
  "  la t0, bng_qx\n" ++
  "  la t1, bnq_Q\n" ++
  "  ld t2, 32(t0); sd t2, 256(t1)\n" ++
  "  ld t2, 40(t0); sd t2, 264(t1)\n" ++
  "  ld t2, 48(t0); sd t2, 272(t1)\n" ++
  "  ld t2, 56(t0); sd t2, 280(t1)  # X[8] = xc1\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  la t1, bng_qy\n" ++
  "  addi t2, t1, 32\n" ++
  "  sd t2, 0(t0)\n" ++
  "  la t2, bnq_le_pm9\n" ++
  "  sd t2, 8(t0)\n" ++
  "  sd t1, 16(t0)\n" ++
  "  la t2, bnf_le_p\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t2, bnq_Q\n" ++
  "  addi t2, t2, 480\n" ++
  "  sd t2, 32(t0)                  # Y[3] = yc0 - 9 yc1\n" ++
  "  .4byte 0x8022a073\n" ++
  "  la t0, bng_qy\n" ++
  "  la t1, bnq_Q\n" ++
  "  ld t2, 32(t0); sd t2, 672(t1)\n" ++
  "  ld t2, 40(t0); sd t2, 680(t1)\n" ++
  "  ld t2, 48(t0); sd t2, 688(t1)\n" ++
  "  ld t2, 56(t0); sd t2, 696(t1)  # Y[9] = yc1\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 768(t1)                 # Z = one\n" ++
  "  jal ra, bnq_miller_accumulate\n" ++
  ".Lbnpair_next:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lbnpair_loop\n" ++
  ".Lbnpair_finish:\n" ++
  -- F = (tn * td^-1)^((p^12-1)/n); result = (F == one)
  "  la a0, bnq_m0\n" ++
  "  la a1, bnq_td\n" ++
  "  la a2, bnq_exp_p12m2_le\n" ++
  "  li a3, 3043\n" ++
  "  jal ra, bnq_pow\n" ++
  q12 "bnq_mul" "bnq_tn" "bnq_tn" "bnq_m0" ++
  "  la a0, bnq_fn\n" ++
  "  la a1, bnq_tn\n" ++
  "  la a2, bnq_exp_final_le\n" ++
  "  li a3, 2789\n" ++
  "  jal ra, bnq_pow\n" ++
  "  la a0, bnq_m0\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  la a0, bnq_fn\n" ++
  "  la a1, bnq_m0\n" ++
  "  jal ra, bnq_eq\n" ++
  "  sb a0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbnpair_ret\n" ++
  ".Lbnpair_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lbnpair_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- The full pairing kernel suite, ON TOP of the bnf_/bnc_ BE suites
    (`bn254PrecompileFunctions`) which dispatcher closures already link. -/
def bn254PairingKernelFunctions : String :=
  bn254Fp2CommonFunctions ++ "\n" ++
  bn254Fq12CommonFunctions ++ "\n" ++
  bn254Fq12PointCommonFunctions ++ "\n" ++
  bn254G2CommonFunctions ++ "\n" ++
  bn254PtCopyFunction ++ "\n" ++
  bn254MillerFunction ++ "\n" ++
  zkvmBn254PairingRealFunction

/-- All pairing data fragments (appended after the field/curve fragments). -/
def bn254PairingAllDataFragments : String :=
  bn254Fp2DataFragment ++
  bn254Fq12DataFragment ++
  bn254Fq12PointDataFragment ++
  bn254PairingDataFragment

/-- Probe: input = k (u64) || k × 192-byte BE pairs. Output: status u64
    at OUTPUT+0, result byte at OUTPUT+8. -/
def ziskBn254PairingRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  ld a1, 0(s0)\n" ++
  "  addi a0, s0, 8\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bn254_pairing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbn254_pairing_probe_done\n" ++
  bn254PrecompileFunctions ++ "\n" ++
  bn254PairingKernelFunctions ++ "\n" ++
  ".Lbn254_pairing_probe_done:"


end EvmAsm.Codegen
