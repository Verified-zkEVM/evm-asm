/-
  EvmAsm.Codegen.Programs.Bn254Fq12Point

  FQ12 projective point arithmetic + the Miller-loop line function for
  the alt_bn128 ecPairing precompile (0x08), bead
  evm-asm-fhsxz.2.4.2.62.10.1 layer 3a.

  Ports py_ecc `optimized_bn128.optimized_curve.double/add` and
  `optimized_pairing.linefunc` verbatim onto the `bnq_*` FQ12 machine
  (`Bn254Fq12.lean`). A point is a 1152-byte buffer of three 384-byte
  FQ12 coordinates (X || Y || Z, projective x = X/Z, y = Y/Z; the
  identity has Z = 0).

  `bnq_mul` composes its product in `bnq_acc` and copies out, so its
  dst may alias either input; all routines below compute into the
  static temp pool `bnq_d0..bnq_d9` and write the destination point
  last, making dst-aliases-src safe throughout.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Bn254Fq12

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- FQ12 point-op temp pool (10 × 384 B). -/
def bn254Fq12PointDataFragment : String :=
  ".balign 8\n" ++
  "bnq_d0:\n  .zero 384\n" ++
  "bnq_d1:\n  .zero 384\n" ++
  "bnq_d2:\n  .zero 384\n" ++
  "bnq_d3:\n  .zero 384\n" ++
  "bnq_d4:\n  .zero 384\n" ++
  "bnq_d5:\n  .zero 384\n" ++
  "bnq_d6:\n  .zero 384\n" ++
  "bnq_d7:\n  .zero 384\n" ++
  "bnq_d8:\n  .zero 384\n" ++
  "bnq_d9:\n  .zero 384\n"

private def call3 (fn d a b : String) : String :=
  "  la a0, " ++ d ++ "\n" ++
  "  la a1, " ++ a ++ "\n" ++
  "  la a2, " ++ b ++ "\n" ++
  "  jal ra, " ++ fn ++ "\n"

/-- Double an FQ12 projective point (py_ecc `optimized_curve.double`):
    W = 3x^2, S = yz, B = xyS, H = W^2 - 8B,
    X' = 2HS, Y' = W(4B - H) - 8 y^2 S^2, Z' = 8 S^3.
    a0 = dst point, a1 = src point; dst may alias src. The identity
    (Z = 0) maps to itself (S = 0 forces Z' = 0). -/
def bn254Fq12PtDoubleFunction : String :=
  "bnq_pt_double:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  -- d0 = x^2 ; d1 = W = 3 x^2
  "  la a0, bnq_d0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d1\n" ++
  "  la a1, bnq_d0\n" ++
  "  la a2, bnq_le_3\n" ++
  "  jal ra, bnq_smul\n" ++
  -- d2 = S = y z
  "  la a0, bnq_d2\n" ++
  "  addi a1, s1, 384\n" ++
  "  addi a2, s1, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  -- d4 = B = x y S
  "  la a0, bnq_d3\n" ++
  "  mv a1, s1\n" ++
  "  addi a2, s1, 384\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_mul" "bnq_d4" "bnq_d3" "bnq_d2" ++
  -- d5 = H = W^2 - 8B
  call3 "bnq_mul" "bnq_d5" "bnq_d1" "bnq_d1" ++
  call3 "bnq_smul" "bnq_d6" "bnq_d4" "bnq_le_8" ++
  call3 "bnq_sub" "bnq_d5" "bnq_d5" "bnq_d6" ++
  -- d7 = X' = 2 H S
  call3 "bnq_mul" "bnq_d6" "bnq_d5" "bnq_d2" ++
  call3 "bnq_smul" "bnq_d7" "bnq_d6" "bnq_le_2" ++
  -- d6 = S^2
  call3 "bnq_mul" "bnq_d6" "bnq_d2" "bnq_d2" ++
  -- d8 = 8 y^2 S^2
  "  la a0, bnq_d8\n" ++
  "  addi a1, s1, 384\n" ++
  "  addi a2, s1, 384\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_mul" "bnq_d8" "bnq_d8" "bnq_d6" ++
  call3 "bnq_smul" "bnq_d8" "bnq_d8" "bnq_le_8" ++
  -- d0 = Y' = W (4B - H) - 8 y^2 S^2
  call3 "bnq_smul" "bnq_d0" "bnq_d4" "bnq_le_4" ++
  call3 "bnq_sub" "bnq_d0" "bnq_d0" "bnq_d5" ++
  call3 "bnq_mul" "bnq_d0" "bnq_d1" "bnq_d0" ++
  call3 "bnq_sub" "bnq_d0" "bnq_d0" "bnq_d8" ++
  -- d6 = Z' = 8 S^3
  call3 "bnq_mul" "bnq_d6" "bnq_d2" "bnq_d6" ++
  call3 "bnq_smul" "bnq_d6" "bnq_d6" "bnq_le_8" ++
  -- write X'/Y'/Z'
  "  la a0, bnq_d7\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_d0\n" ++
  "  addi a1, s0, 384\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_d6\n" ++
  "  addi a1, s0, 768\n" ++
  "  jal ra, bnq_copy\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Add two FQ12 projective points (py_ecc `optimized_curve.add`).
    a0 = dst, a1 = p1, a2 = p2; dst may alias p1/p2. -/
def bn254Fq12PtAddFunction : String :=
  "bnq_pt_add:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  addi a0, s1, 768\n" ++
  "  jal ra, bnq_is_zero\n" ++
  "  beqz a0, .Lbnq_ptadd_p1fin\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, .Lbnq_ptadd_copy_pt    # dst = p2\n" ++
  "  j .Lbnq_ptadd_ret\n" ++
  ".Lbnq_ptadd_p1fin:\n" ++
  "  addi a0, s2, 768\n" ++
  "  jal ra, bnq_is_zero\n" ++
  "  beqz a0, .Lbnq_ptadd_p2fin\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, .Lbnq_ptadd_copy_pt    # dst = p1\n" ++
  "  j .Lbnq_ptadd_ret\n" ++
  ".Lbnq_ptadd_p2fin:\n" ++
  -- d0 = U1 = y2 z1 ; d1 = U2 = y1 z2 ; d2 = V1 = x2 z1 ; d3 = V2 = x1 z2
  "  la a0, bnq_d0\n" ++
  "  addi a1, s2, 384\n" ++
  "  addi a2, s1, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d1\n" ++
  "  addi a1, s1, 384\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d2\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s1, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d3\n" ++
  "  mv a1, s1\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d2\n" ++
  "  la a1, bnq_d3\n" ++
  "  jal ra, bnq_eq\n" ++
  "  beqz a0, .Lbnq_ptadd_general\n" ++
  "  la a0, bnq_d0\n" ++
  "  la a1, bnq_d1\n" ++
  "  jal ra, bnq_eq\n" ++
  "  beqz a0, .Lbnq_ptadd_inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnq_pt_double          # equal points\n" ++
  "  j .Lbnq_ptadd_ret\n" ++
  ".Lbnq_ptadd_inf:\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  addi a0, s0, 384\n" ++
  "  jal ra, bnq_set_one\n" ++
  "  addi a0, s0, 768\n" ++
  "  jal ra, bnq_zero               # (one, one, zero)\n" ++
  "  j .Lbnq_ptadd_ret\n" ++
  ".Lbnq_ptadd_general:\n" ++
  -- d4 = U = U1 - U2 ; d5 = V = V1 - V2
  call3 "bnq_sub" "bnq_d4" "bnq_d0" "bnq_d1" ++
  call3 "bnq_sub" "bnq_d5" "bnq_d2" "bnq_d3" ++
  -- d6 = V^2 ; d7 = V^2 V2 ; d6 = V^3
  call3 "bnq_mul" "bnq_d6" "bnq_d5" "bnq_d5" ++
  call3 "bnq_mul" "bnq_d7" "bnq_d6" "bnq_d3" ++
  call3 "bnq_mul" "bnq_d6" "bnq_d6" "bnq_d5" ++
  -- d8 = W = z1 z2
  "  la a0, bnq_d8\n" ++
  "  addi a1, s1, 768\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  -- d9 = A = U^2 W - V^3 - 2 V^2 V2
  call3 "bnq_mul" "bnq_d9" "bnq_d4" "bnq_d4" ++
  call3 "bnq_mul" "bnq_d9" "bnq_d9" "bnq_d8" ++
  call3 "bnq_sub" "bnq_d9" "bnq_d9" "bnq_d6" ++
  call3 "bnq_smul" "bnq_d0" "bnq_d7" "bnq_le_2" ++
  call3 "bnq_sub" "bnq_d9" "bnq_d9" "bnq_d0" ++
  -- d0 = X' = V A
  call3 "bnq_mul" "bnq_d0" "bnq_d5" "bnq_d9" ++
  -- d7 = Y' = U (V^2 V2 - A) - V^3 U2
  call3 "bnq_sub" "bnq_d7" "bnq_d7" "bnq_d9" ++
  call3 "bnq_mul" "bnq_d7" "bnq_d4" "bnq_d7" ++
  call3 "bnq_mul" "bnq_d3" "bnq_d6" "bnq_d1" ++
  call3 "bnq_sub" "bnq_d7" "bnq_d7" "bnq_d3" ++
  -- d6 = Z' = V^3 W
  call3 "bnq_mul" "bnq_d6" "bnq_d6" "bnq_d8" ++
  "  la a0, bnq_d0\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_d7\n" ++
  "  addi a1, s0, 384\n" ++
  "  jal ra, bnq_copy\n" ++
  "  la a0, bnq_d6\n" ++
  "  addi a1, s0, 768\n" ++
  "  jal ra, bnq_copy\n" ++
  ".Lbnq_ptadd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret\n" ++
  -- local subroutine: copy the 1152-byte point at a0 to a1
  ".Lbnq_ptadd_copy_pt:\n" ++
  "  li t2, 144\n" ++
  ".Lbnq_ptadd_copy_loop:\n" ++
  "  ld t3, 0(a0)\n" ++
  "  sd t3, 0(a1)\n" ++
  "  addi a0, a0, 8\n" ++
  "  addi a1, a1, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lbnq_ptadd_copy_loop\n" ++
  "  ret"

/-- py_ecc `optimized_pairing.linefunc`: the (numerator, denominator)
    of the line through projective P1/P2 evaluated at T.
    a0 = num dst (FQ12), a1 = den dst, a2 = P1, a3 = P2, a4 = T.
    dst cells must not be in the bnq_d pool. -/
def bn254Fq12LinefuncFunction : String :=
  "bnq_linefunc:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++
  "  mv s4, a4\n" ++
  -- d0 = m_num = y2 z1 - y1 z2
  "  la a0, bnq_d0\n" ++
  "  addi a1, s3, 384\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d1\n" ++
  "  addi a1, s2, 384\n" ++
  "  addi a2, s3, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_sub" "bnq_d0" "bnq_d0" "bnq_d1" ++
  -- d1 = m_den = x2 z1 - x1 z2
  "  la a0, bnq_d1\n" ++
  "  mv a1, s3\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d2\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s3, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_sub" "bnq_d1" "bnq_d1" "bnq_d2" ++
  "  la a0, bnq_d1\n" ++
  "  jal ra, bnq_is_zero\n" ++
  "  beqz a0, .Lbnq_lf_have_m\n" ++
  "  la a0, bnq_d0\n" ++
  "  jal ra, bnq_is_zero\n" ++
  "  beqz a0, .Lbnq_lf_vertical\n" ++
  -- tangent: m_num = 3 x1^2, m_den = 2 y1 z1
  "  la a0, bnq_d2\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_smul" "bnq_d0" "bnq_d2" "bnq_le_3" ++
  "  la a0, bnq_d2\n" ++
  "  addi a1, s2, 384\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_smul" "bnq_d1" "bnq_d2" "bnq_le_2" ++
  ".Lbnq_lf_have_m:\n" ++
  -- d2 = xt z1 - x1 zt
  "  la a0, bnq_d2\n" ++
  "  mv a1, s4\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d3\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s4, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_sub" "bnq_d2" "bnq_d2" "bnq_d3" ++
  -- d3 = yt z1 - y1 zt
  "  la a0, bnq_d3\n" ++
  "  addi a1, s4, 384\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d4\n" ++
  "  addi a1, s2, 384\n" ++
  "  addi a2, s4, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  call3 "bnq_sub" "bnq_d3" "bnq_d3" "bnq_d4" ++
  -- num = m_num d2 - m_den d3 ; den = m_den zt z1
  call3 "bnq_mul" "bnq_d2" "bnq_d0" "bnq_d2" ++
  call3 "bnq_mul" "bnq_d3" "bnq_d1" "bnq_d3" ++
  "  la a1, bnq_d2\n" ++
  "  la a2, bnq_d3\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, bnq_sub\n" ++
  "  la a0, bnq_d2\n" ++
  "  la a1, bnq_d1\n" ++
  "  addi a2, s4, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  mv a0, s1\n" ++
  "  la a1, bnq_d2\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  j .Lbnq_lf_ret\n" ++
  ".Lbnq_lf_vertical:\n" ++
  -- num = xt z1 - x1 zt ; den = z1 zt
  "  la a0, bnq_d2\n" ++
  "  mv a1, s4\n" ++
  "  addi a2, s2, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  la a0, bnq_d3\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s4, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  "  mv a0, s0\n" ++
  "  la a1, bnq_d2\n" ++
  "  la a2, bnq_d3\n" ++
  "  jal ra, bnq_sub\n" ++
  "  mv a0, s1\n" ++
  "  addi a1, s2, 768\n" ++
  "  addi a2, s4, 768\n" ++
  "  jal ra, bnq_mul\n" ++
  ".Lbnq_lf_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

def bn254Fq12PointCommonFunctions : String :=
  bn254Fq12PtDoubleFunction ++ "\n" ++
  bn254Fq12PtAddFunction ++ "\n" ++
  bn254Fq12LinefuncFunction

end EvmAsm.Codegen
