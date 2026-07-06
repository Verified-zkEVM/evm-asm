/-
  EvmAsm.Codegen.Programs.Bls12Pairing

  The EIP-2537 BLS12-381 pairing (0x0f) kernel: FQ12 projective point
  arithmetic, the py_ecc-mirroring Miller loop, and
  `zkvm_bls12_pairing`. Clones the proven BN254 recipe
  (Bn254Fq12Point / Bn254PairingCore / Bn254Pairing, PR #8731) onto the
  `blq_*` machine (Bls12Fq12.lean).

  Algorithm = execution-specs `bls12_pairing`, which computes
  ∏ pairing(Q_i, P_i) with py_ecc `optimized_bls12_381`. Same two exact
  hoisting rewrites as BN254: cross-pair num/den accumulation with ONE
  Fermat inverse (x^(p^12-2)) and ONE final exponentiation
  (x^((p^12-1)/n)). BLS simplifications vs BN254:

    * pseudo_binary_encoding[62::-1] has no -1 entries — the add step
      always uses Q (no negated copy);
    * the loop has NO Frobenius extra lines (py_ecc comments them out):
      f = f_num / f_den right after the 63 iterations.

  py_ecc `twist` (Fp2 -> FQ12, u^2 = -1 -> w^2 - 2w + 2 isomorphism
  coeffs [c0 - c1, c1]): X lands in coefficients 1 and 7, Y in 0 and 6,
  Z in 3 and 9 — so the twisted Q has Z = w^3 (coefficient 3 = one).

  EIP-2537 input validation per pair (384 bytes = 128-byte G1 wire +
  256-byte G2 wire): decode via the existing `blsg_decode_g1` /
  `blsg2_decode_g2` (pad-zero + coord < p + on-curve), and REAL
  subgroup checks on BOTH sides (`blsg_subgroup_g1` — the G1 cofactor
  is not 1 — and `blsg2_subgroup_g2`). Kernel ABI:

    zkvm_bls12_pairing(a0 = raw input (384·k), a1 = k, a2 = result ptr)
      -> a0 = 0 ok (result byte = 1 iff the product is one),
         a0 = 1 invalid input (execution-specs precompile failure).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.Bls12Fq12

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Pairing data labels WITHOUT a `.section .data` header. -/
def bls12PairingDataFragment : String :=
  ".balign 8\n" ++
  -- py_ecc pseudo_binary_encoding[62::-1] (bits 62..0 of the ate loop
  -- count 0xD201000000010000; all entries 0/1).
  "blq_pbe:\n" ++
  "  .byte 1,0,1,0,0,1,0,0,0,0,0,0,0,0,1,0\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0\n" ++
  "  .byte 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0\n" ++
  -- FQ12 projective working points (X||Y||Z, 576 B each) and the FQ12
  -- temp pool for the point/line routines.
  ".balign 8\n" ++
  "blq_R:\n  .zero 1728\n" ++
  "blq_Q:\n  .zero 1728\n" ++
  "blq_P:\n  .zero 1728\n" ++
  "blq_ln:\n  .zero 576\n" ++
  "blq_ld:\n  .zero 576\n" ++
  "blq_fn:\n  .zero 576\n" ++
  "blq_fd:\n  .zero 576\n" ++
  "blq_tn:\n  .zero 576\n" ++
  "blq_td:\n  .zero 576\n" ++
  "blq_m0:\n  .zero 576\n" ++
  "blq_d0:\n  .zero 576\n" ++
  "blq_d1:\n  .zero 576\n" ++
  "blq_d2:\n  .zero 576\n" ++
  "blq_d3:\n  .zero 576\n" ++
  "blq_d4:\n  .zero 576\n" ++
  "blq_d5:\n  .zero 576\n" ++
  "blq_d6:\n  .zero 576\n" ++
  "blq_d7:\n  .zero 576\n" ++
  "blq_d8:\n  .zero 576\n" ++
  "blq_d9:\n  .zero 576\n"

private def call3 (fn d a b : String) : String :=
  "  la a0, " ++ d ++ "\n" ++
  "  la a1, " ++ a ++ "\n" ++
  "  la a2, " ++ b ++ "\n" ++
  "  jal ra, " ++ fn ++ "\n"

/-- Copy a 1728-byte FQ12 projective point: a0 = src, a1 = dst. -/
def blqPtCopy_prog : Program :=
  [ .LI .x7 (216 : Word),
    .LD .x28 .x10 (0 : BitVec 12),
    .SD .x11 .x28 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12PtCopyFunction : String :=
  "blq_pt_copy:\n" ++ emitProgram blqPtCopy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blqPtCopy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12PtCopyFunction_eq_prog :
    bls12PtCopyFunction = "blq_pt_copy:\n" ++ emitProgram blqPtCopy_prog := rfl

#guard bls12PtCopyFunction.startsWith "blq_pt_copy:\n"
#guard blqPtCopy_prog.length = 8
/-- Double an FQ12 projective point (py_ecc `optimized_curve.double`):
    W = 3x^2, S = yz, B = xyS, H = W^2 - 8B,
    X' = 2HS, Y' = W(4B - H) - 8 y^2 S^2, Z' = 8 S^3.
    a0 = dst point, a1 = src point; dst may alias src. -/
def bls12PtDoubleFunction : String :=
  "blq_pt_double:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  -- d0 = x^2 ; d1 = W = 3 x^2
  "  la a0, blq_d0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d1\n" ++
  "  la a1, blq_d0\n" ++
  "  la a2, blq_le_3\n" ++
  "  jal ra, blq_smul\n" ++
  -- d2 = S = y z
  "  la a0, blq_d2\n" ++
  "  addi a1, s1, 576\n" ++
  "  addi a2, s1, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  -- d4 = B = x y S
  "  la a0, blq_d3\n" ++
  "  mv a1, s1\n" ++
  "  addi a2, s1, 576\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_mul" "blq_d4" "blq_d3" "blq_d2" ++
  -- d5 = H = W^2 - 8B
  call3 "blq_mul" "blq_d5" "blq_d1" "blq_d1" ++
  call3 "blq_smul" "blq_d6" "blq_d4" "blq_le_8" ++
  call3 "blq_sub" "blq_d5" "blq_d5" "blq_d6" ++
  -- d7 = X' = 2 H S
  call3 "blq_mul" "blq_d6" "blq_d5" "blq_d2" ++
  call3 "blq_smul" "blq_d7" "blq_d6" "blq_le_2" ++
  -- d6 = S^2
  call3 "blq_mul" "blq_d6" "blq_d2" "blq_d2" ++
  -- d8 = 8 y^2 S^2
  "  la a0, blq_d8\n" ++
  "  addi a1, s1, 576\n" ++
  "  addi a2, s1, 576\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_mul" "blq_d8" "blq_d8" "blq_d6" ++
  call3 "blq_smul" "blq_d8" "blq_d8" "blq_le_8" ++
  -- d0 = Y' = W (4B - H) - 8 y^2 S^2
  call3 "blq_smul" "blq_d0" "blq_d4" "blq_le_4" ++
  call3 "blq_sub" "blq_d0" "blq_d0" "blq_d5" ++
  call3 "blq_mul" "blq_d0" "blq_d1" "blq_d0" ++
  call3 "blq_sub" "blq_d0" "blq_d0" "blq_d8" ++
  -- d6 = Z' = 8 S^3
  call3 "blq_mul" "blq_d6" "blq_d2" "blq_d6" ++
  call3 "blq_smul" "blq_d6" "blq_d6" "blq_le_8" ++
  -- write X'/Y'/Z'
  "  la a0, blq_d7\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blq_copy\n" ++
  "  la a0, blq_d0\n" ++
  "  addi a1, s0, 576\n" ++
  "  jal ra, blq_copy\n" ++
  "  la a0, blq_d6\n" ++
  "  addi a1, s0, 1152\n" ++
  "  jal ra, blq_copy\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Add two FQ12 projective points (py_ecc `optimized_curve.add`).
    a0 = dst, a1 = p1, a2 = p2; dst may alias p1/p2. -/
def bls12PtAddFunction : String :=
  "blq_pt_add:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  addi a0, s1, 1152\n" ++
  "  jal ra, blq_is_zero\n" ++
  "  beqz a0, .Lblq_ptadd_p1fin\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blq_pt_copy            # dst = p2\n" ++
  "  j .Lblq_ptadd_ret\n" ++
  ".Lblq_ptadd_p1fin:\n" ++
  "  addi a0, s2, 1152\n" ++
  "  jal ra, blq_is_zero\n" ++
  "  beqz a0, .Lblq_ptadd_p2fin\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blq_pt_copy            # dst = p1\n" ++
  "  j .Lblq_ptadd_ret\n" ++
  ".Lblq_ptadd_p2fin:\n" ++
  -- d0 = U1 = y2 z1 ; d1 = U2 = y1 z2 ; d2 = V1 = x2 z1 ; d3 = V2 = x1 z2
  "  la a0, blq_d0\n" ++
  "  addi a1, s2, 576\n" ++
  "  addi a2, s1, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d1\n" ++
  "  addi a1, s1, 576\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d2\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s1, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d3\n" ++
  "  mv a1, s1\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d2\n" ++
  "  la a1, blq_d3\n" ++
  "  jal ra, blq_eq\n" ++
  "  beqz a0, .Lblq_ptadd_general\n" ++
  "  la a0, blq_d0\n" ++
  "  la a1, blq_d1\n" ++
  "  jal ra, blq_eq\n" ++
  "  beqz a0, .Lblq_ptadd_inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blq_pt_double          # equal points\n" ++
  "  j .Lblq_ptadd_ret\n" ++
  ".Lblq_ptadd_inf:\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, blq_set_one\n" ++
  "  addi a0, s0, 576\n" ++
  "  jal ra, blq_set_one\n" ++
  "  addi a0, s0, 1152\n" ++
  "  jal ra, blq_zero               # (one, one, zero)\n" ++
  "  j .Lblq_ptadd_ret\n" ++
  ".Lblq_ptadd_general:\n" ++
  -- d4 = U = U1 - U2 ; d5 = V = V1 - V2
  call3 "blq_sub" "blq_d4" "blq_d0" "blq_d1" ++
  call3 "blq_sub" "blq_d5" "blq_d2" "blq_d3" ++
  -- d6 = V^2 ; d7 = V^2 V2 ; d6 = V^3
  call3 "blq_mul" "blq_d6" "blq_d5" "blq_d5" ++
  call3 "blq_mul" "blq_d7" "blq_d6" "blq_d3" ++
  call3 "blq_mul" "blq_d6" "blq_d6" "blq_d5" ++
  -- d8 = W = z1 z2
  "  la a0, blq_d8\n" ++
  "  addi a1, s1, 1152\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  -- d9 = A = U^2 W - V^3 - 2 V^2 V2
  call3 "blq_mul" "blq_d9" "blq_d4" "blq_d4" ++
  call3 "blq_mul" "blq_d9" "blq_d9" "blq_d8" ++
  call3 "blq_sub" "blq_d9" "blq_d9" "blq_d6" ++
  call3 "blq_smul" "blq_d0" "blq_d7" "blq_le_2" ++
  call3 "blq_sub" "blq_d9" "blq_d9" "blq_d0" ++
  -- d0 = X' = V A
  call3 "blq_mul" "blq_d0" "blq_d5" "blq_d9" ++
  -- d7 = Y' = U (V^2 V2 - A) - V^3 U2
  call3 "blq_sub" "blq_d7" "blq_d7" "blq_d9" ++
  call3 "blq_mul" "blq_d7" "blq_d4" "blq_d7" ++
  call3 "blq_mul" "blq_d3" "blq_d6" "blq_d1" ++
  call3 "blq_sub" "blq_d7" "blq_d7" "blq_d3" ++
  -- d6 = Z' = V^3 W
  call3 "blq_mul" "blq_d6" "blq_d6" "blq_d8" ++
  "  la a0, blq_d0\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blq_copy\n" ++
  "  la a0, blq_d7\n" ++
  "  addi a1, s0, 576\n" ++
  "  jal ra, blq_copy\n" ++
  "  la a0, blq_d6\n" ++
  "  addi a1, s0, 1152\n" ++
  "  jal ra, blq_copy\n" ++
  ".Lblq_ptadd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- py_ecc `optimized_pairing.linefunc`: the (numerator, denominator)
    of the line through projective P1/P2 evaluated at T.
    a0 = num dst (FQ12), a1 = den dst, a2 = P1, a3 = P2, a4 = T.
    dst cells must not be in the blq_d pool. -/
def bls12LinefuncFunction : String :=
  "blq_linefunc:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  mv s3, a3\n" ++
  "  mv s4, a4\n" ++
  -- d0 = m_num = y2 z1 - y1 z2
  "  la a0, blq_d0\n" ++
  "  addi a1, s3, 576\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d1\n" ++
  "  addi a1, s2, 576\n" ++
  "  addi a2, s3, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_sub" "blq_d0" "blq_d0" "blq_d1" ++
  -- d1 = m_den = x2 z1 - x1 z2
  "  la a0, blq_d1\n" ++
  "  mv a1, s3\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d2\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s3, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_sub" "blq_d1" "blq_d1" "blq_d2" ++
  "  la a0, blq_d1\n" ++
  "  jal ra, blq_is_zero\n" ++
  "  beqz a0, .Lblq_lf_have_m\n" ++
  "  la a0, blq_d0\n" ++
  "  jal ra, blq_is_zero\n" ++
  "  beqz a0, .Lblq_lf_vertical\n" ++
  -- tangent: m_num = 3 x1^2, m_den = 2 y1 z1
  "  la a0, blq_d2\n" ++
  "  mv a1, s2\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_smul" "blq_d0" "blq_d2" "blq_le_3" ++
  "  la a0, blq_d2\n" ++
  "  addi a1, s2, 576\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_smul" "blq_d1" "blq_d2" "blq_le_2" ++
  ".Lblq_lf_have_m:\n" ++
  -- d2 = xt z1 - x1 zt
  "  la a0, blq_d2\n" ++
  "  mv a1, s4\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d3\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s4, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_sub" "blq_d2" "blq_d2" "blq_d3" ++
  -- d3 = yt z1 - y1 zt
  "  la a0, blq_d3\n" ++
  "  addi a1, s4, 576\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d4\n" ++
  "  addi a1, s2, 576\n" ++
  "  addi a2, s4, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  call3 "blq_sub" "blq_d3" "blq_d3" "blq_d4" ++
  -- num = m_num d2 - m_den d3 ; den = m_den zt z1
  call3 "blq_mul" "blq_d2" "blq_d0" "blq_d2" ++
  call3 "blq_mul" "blq_d3" "blq_d1" "blq_d3" ++
  "  la a1, blq_d2\n" ++
  "  la a2, blq_d3\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, blq_sub\n" ++
  "  la a0, blq_d2\n" ++
  "  la a1, blq_d1\n" ++
  "  addi a2, s4, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blq_d2\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  j .Lblq_lf_ret\n" ++
  ".Lblq_lf_vertical:\n" ++
  -- num = xt z1 - x1 zt ; den = z1 zt
  "  la a0, blq_d2\n" ++
  "  mv a1, s4\n" ++
  "  addi a2, s2, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  la a0, blq_d3\n" ++
  "  mv a1, s2\n" ++
  "  addi a2, s4, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blq_d2\n" ++
  "  la a2, blq_d3\n" ++
  "  jal ra, blq_sub\n" ++
  "  mv a0, s1\n" ++
  "  addi a1, s2, 1152\n" ++
  "  addi a2, s4, 1152\n" ++
  "  jal ra, blq_mul\n" ++
  ".Lblq_lf_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

private def q12 (fn d a b : String) : String :=
  "  la a0, " ++ d ++ "\n" ++
  "  la a1, " ++ a ++ "\n" ++
  "  la a2, " ++ b ++ "\n" ++
  "  jal ra, " ++ fn ++ "\n"

/-- py_ecc `miller_loop(Q, P, final_exponentiate=False)` accumulated as
    a fraction: multiplies `blq_tn` by f_num and `blq_td` by f_den.
    Expects the twisted Q in `blq_Q` and the cast P in `blq_P` (both
    finite). No -1 encoding entries and no Frobenius tail for BLS. -/
def bls12MillerFunction : String :=
  "blq_miller_accumulate:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s3, 8(sp); sd s4, 16(sp)\n" ++
  "  la a0, blq_Q\n" ++
  "  la a1, blq_R\n" ++
  "  jal ra, blq_pt_copy\n" ++
  "  la a0, blq_fn\n" ++
  "  jal ra, blq_set_one\n" ++
  "  la a0, blq_fd\n" ++
  "  jal ra, blq_set_one\n" ++
  "  li s3, 0                       # iteration index\n" ++
  ".Lblq_ml_loop:\n" ++
  -- doubling step: f = f^2 * line(R, R, P) ; R = 2R
  "  la a0, blq_ln\n" ++
  "  la a1, blq_ld\n" ++
  "  la a2, blq_R\n" ++
  "  la a3, blq_R\n" ++
  "  la a4, blq_P\n" ++
  "  jal ra, blq_linefunc\n" ++
  q12 "blq_mul" "blq_m0" "blq_fn" "blq_fn" ++
  q12 "blq_mul" "blq_fn" "blq_m0" "blq_ln" ++
  q12 "blq_mul" "blq_m0" "blq_fd" "blq_fd" ++
  q12 "blq_mul" "blq_fd" "blq_m0" "blq_ld" ++
  "  la a0, blq_R\n" ++
  "  la a1, blq_R\n" ++
  "  jal ra, blq_pt_double\n" ++
  "  la t0, blq_pbe\n" ++
  "  add t0, t0, s3\n" ++
  "  lbu s4, 0(t0)\n" ++
  "  beqz s4, .Lblq_ml_next\n" ++
  -- addition step: f *= line(R, Q, P) ; R = R + Q
  "  la a0, blq_ln\n" ++
  "  la a1, blq_ld\n" ++
  "  la a2, blq_R\n" ++
  "  la a3, blq_Q\n" ++
  "  la a4, blq_P\n" ++
  "  jal ra, blq_linefunc\n" ++
  q12 "blq_mul" "blq_fn" "blq_fn" "blq_ln" ++
  q12 "blq_mul" "blq_fd" "blq_fd" "blq_ld" ++
  q12 "blq_pt_add" "blq_R" "blq_R" "blq_Q" ++
  ".Lblq_ml_next:\n" ++
  "  addi s3, s3, 1\n" ++
  "  li t0, 63\n" ++
  "  bne s3, t0, .Lblq_ml_loop\n" ++
  -- accumulate across pairs
  q12 "blq_mul" "blq_tn" "blq_tn" "blq_fn" ++
  q12 "blq_mul" "blq_td" "blq_td" "blq_fd" ++
  "  ld ra, 0(sp); ld s3, 8(sp); ld s4, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- Real BLS12-381 pairing kernel. a0 = raw EIP-2537 input (384·k:
    128-byte G1 wire + 256-byte G2 wire per pair), a1 = k, a2 = result
    byte pointer. Returns a0 = 0 (result byte = 1 iff the product is
    one) or a0 = 1 on invalid input (bad encoding, off-curve, or either
    point outside its order-n subgroup). -/
def zkvmBls12PairingRealFunction : String :=
  ".globl zkvm_bls12_pairing\n" ++
  "zkvm_bls12_pairing:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la a0, blq_tn\n" ++
  "  jal ra, blq_set_one\n" ++
  "  la a0, blq_td\n" ++
  "  jal ra, blq_set_one\n" ++
  "  li s3, 0                       # pair index\n" ++
  ".Lblpair_loop:\n" ++
  "  bgeu s3, s1, .Lblpair_finish\n" ++
  "  li t0, 384\n" ++
  "  mul t0, t0, s3\n" ++
  "  add s6, s0, t0                 # this pair's base\n" ++
  -- G1: wire decode (pad + range + curve) into the compact BE cell.
  "  mv a0, s6\n" ++
  "  la a1, blsg_pt1\n" ++
  "  jal ra, blsg_decode_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblpair_invalid\n" ++
  "  mv s4, a0                      # 1 = P at infinity\n" ++
  -- EIP-2537: G1 subgroup check (the cofactor is not 1) on finite P.
  "  bnez s4, .Lblpair_g1_ok\n" ++
  "  la a0, blsg_pt1\n" ++
  "  jal ra, blsg_subgroup_g1\n" ++
  "  beqz a0, .Lblpair_invalid\n" ++
  ".Lblpair_g1_ok:\n" ++
  -- G2: wire decode (pad + range + curve) into the LE affine cell.
  "  addi a0, s6, 128\n" ++
  "  la a1, blsg2_pt1\n" ++
  "  jal ra, blsg2_decode_g2\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblpair_invalid\n" ++
  "  mv s5, a0                      # 1 = Q at infinity\n" ++
  "  bnez s5, .Lblpair_g2_ok\n" ++
  "  la a0, blsg2_pt1\n" ++
  "  jal ra, blsg2_subgroup_g2\n" ++
  "  beqz a0, .Lblpair_invalid\n" ++
  ".Lblpair_g2_ok:\n" ++
  -- pairing(Q, P) = one when either is at infinity: skip.
  "  or t0, s4, s5\n" ++
  "  bnez t0, .Lblpair_next\n" ++
  -- cast P to FQ12 projective: X = (xP, 0...), Y = (yP, 0...), Z = one.
  "  la a0, blq_P\n" ++
  "  jal ra, blq_zero\n" ++
  "  la a0, blq_P\n" ++
  "  addi a0, a0, 576\n" ++
  "  jal ra, blq_zero\n" ++
  "  la a0, blq_P\n" ++
  "  addi a0, a0, 1152\n" ++
  "  jal ra, blq_zero\n" ++
  "  la a0, blsg_pt1\n" ++
  "  la a1, blq_P\n" ++
  "  jal ra, blsg_be_to_le          # X[0] = xP\n" ++
  "  la a0, blsg_pt1\n" ++
  "  addi a0, a0, 48\n" ++
  "  la a1, blq_P\n" ++
  "  addi a1, a1, 576\n" ++
  "  jal ra, blsg_be_to_le          # Y[0] = yP\n" ++
  "  la t1, blq_P\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 1152(t1)                # Z = one\n" ++
  -- twist Q into blq_Q (LE coords xc0/xc1/yc0/yc1 at +0/48/96/144):
  -- X[1] = xc0 - xc1, X[7] = xc1, Y[0] = yc0 - yc1, Y[6] = yc1,
  -- Z = w^3 (coefficient 3 = one).
  "  la a0, blq_Q\n" ++
  "  jal ra, blq_zero\n" ++
  "  la a0, blq_Q\n" ++
  "  addi a0, a0, 576\n" ++
  "  jal ra, blq_zero\n" ++
  "  la a0, blq_Q\n" ++
  "  addi a0, a0, 1152\n" ++
  "  jal ra, blq_zero\n" ++
  "  la t0, blq_arith_params\n" ++
  "  la t1, blsg2_pt1\n" ++
  "  addi t2, t1, 48\n" ++
  "  sd t2, 0(t0)                   # a = xc1\n" ++
  "  la t2, blsg2_pm1_le\n" ++
  "  sd t2, 8(t0)                   # b = p - 1\n" ++
  "  sd t1, 16(t0)                  # c = xc0\n" ++
  "  la t2, blsf_le_p\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t2, blq_Q\n" ++
  "  addi t2, t2, 48\n" ++
  "  sd t2, 32(t0)                  # X[1] = xc0 - xc1\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073\n" ++
  "  la t0, blsg2_pt1\n" ++
  "  la t1, blq_Q\n" ++
  "  ld t2, 48(t0); sd t2, 336(t1)\n" ++
  "  ld t2, 56(t0); sd t2, 344(t1)\n" ++
  "  ld t2, 64(t0); sd t2, 352(t1)\n" ++
  "  ld t2, 72(t0); sd t2, 360(t1)\n" ++
  "  ld t2, 80(t0); sd t2, 368(t1)\n" ++
  "  ld t2, 88(t0); sd t2, 376(t1)  # X[7] = xc1\n" ++
  "  la t0, blq_arith_params\n" ++
  "  la t1, blsg2_pt1\n" ++
  "  addi t2, t1, 144\n" ++
  "  sd t2, 0(t0)                   # a = yc1\n" ++
  "  la t2, blsg2_pm1_le\n" ++
  "  sd t2, 8(t0)\n" ++
  "  addi t2, t1, 96\n" ++
  "  sd t2, 16(t0)                  # c = yc0\n" ++
  "  la t2, blsf_le_p\n" ++
  "  sd t2, 24(t0)\n" ++
  "  la t2, blq_Q\n" ++
  "  addi t2, t2, 576\n" ++
  "  sd t2, 32(t0)                  # Y[0] = yc0 - yc1\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073\n" ++
  "  la t0, blsg2_pt1\n" ++
  "  la t1, blq_Q\n" ++
  "  ld t2, 144(t0); sd t2, 864(t1)\n" ++
  "  ld t2, 152(t0); sd t2, 872(t1)\n" ++
  "  ld t2, 160(t0); sd t2, 880(t1)\n" ++
  "  ld t2, 168(t0); sd t2, 888(t1)\n" ++
  "  ld t2, 176(t0); sd t2, 896(t1)\n" ++
  "  ld t2, 184(t0); sd t2, 904(t1) # Y[6] = yc1\n" ++
  "  li t2, 1\n" ++
  "  sd t2, 1296(t1)                # Z = w^3 (coefficient 3 = one)\n" ++
  "  jal ra, blq_miller_accumulate\n" ++
  ".Lblpair_next:\n" ++
  "  addi s3, s3, 1\n" ++
  "  j .Lblpair_loop\n" ++
  ".Lblpair_finish:\n" ++
  -- F = (tn * td^-1)^((p^12-1)/n); result = (F == one)
  "  la a0, blq_m0\n" ++
  "  la a1, blq_td\n" ++
  "  la a2, blq_exp_p12m2_le\n" ++
  "  li a3, 4568\n" ++
  "  jal ra, blq_pow\n" ++
  q12 "blq_mul" "blq_tn" "blq_tn" "blq_m0" ++
  "  la a0, blq_fn\n" ++
  "  la a1, blq_tn\n" ++
  "  la a2, blq_exp_final_le\n" ++
  "  li a3, 4313\n" ++
  "  jal ra, blq_pow\n" ++
  "  la a0, blq_m0\n" ++
  "  jal ra, blq_set_one\n" ++
  "  la a0, blq_fn\n" ++
  "  la a1, blq_m0\n" ++
  "  jal ra, blq_eq\n" ++
  "  sb a0, 0(s2)\n" ++
  "  li a0, 0\n" ++
  "  j .Lblpair_ret\n" ++
  ".Lblpair_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblpair_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"

/-- The full BLS pairing kernel suite, ON TOP of the blsg_/blsg2_
    suites (Bls12G1/Bls12G2) which dispatcher closures already link. -/
def bls12PairingKernelFunctions : String :=
  bls12Fq12CommonFunctions ++ "\n" ++
  bls12PtCopyFunction ++ "\n" ++
  bls12PtDoubleFunction ++ "\n" ++
  bls12PtAddFunction ++ "\n" ++
  bls12LinefuncFunction ++ "\n" ++
  bls12MillerFunction ++ "\n" ++
  zkvmBls12PairingRealFunction

/-- All pairing data fragments (appended after the field/G1/G2 fragments). -/
def bls12PairingAllDataFragments : String :=
  bls12Fq12DataFragment ++
  bls12PairingDataFragment

/-- Probe: input = k (u64) || k × 384-byte EIP-2537 wire pairs.
    Output: status u64 at OUTPUT+0, result byte at OUTPUT+8. -/
def ziskBls12PairingRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  ld a1, 0(s0)\n" ++
  "  addi a0, s0, 8\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_pairing\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbls12_pairing_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  bls12PairingKernelFunctions ++ "\n" ++
  ".Lbls12_pairing_probe_done:"

def ziskBls12PairingRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12PairingRealProbePrologue
  dataAsm     :=
    bls12G2DataSection ++
    bls12PairingAllDataFragments
}

end EvmAsm.Codegen
