/-
  EvmAsm.Codegen.Programs.Bls12G2

  Affine BLS12-381 G2 curve layer plus the runtime EIP-2537 precompile
  kernels `zkvm_bls12_g2_add` (0x0d) and `zkvm_bls12_g2_msm` (0x0e).

  G2 lives over Fp2 = Fp[u]/(u^2 + 1) on y^2 = x^3 + 4(u + 1). There is
  no G2 curve accelerator, so the chord/tangent formulas are software,
  built from single-syscall Fp2 ops:

    * Bls12_381ComplexAdd/Sub/Mul  csrs 0x80E/0x80F/0x810 — one call per
      Fp2 add/sub/mul on 96-byte LE-limb buffers (c0 || c1), mutating
      dst ◦= src via the shared `blsf_cplx_params` block;
    * Arith384Mod  csrs 0x80B — Fp mul/add for the Fp2 norm, the Fermat
      inverse (x^(p-2), ~570 calls), and negation (mul by p-1).

  Points stay in the accelerators' native LE-limb format internally (an
  affine point = 192-byte x || y, infinity = all-zero — (0,0) is not on
  the curve); big-endian conversion happens only at the EIP-2537 wire
  boundary. One affine point op costs ~1 Fp inversion (~9k steps), a
  scalar mul ~3.5M steps, so a worst-case 128-pair MSM (subgroup check +
  term mul per pair) stays under the 1e9 stateless budget.

  Wire format (execution-specs bls12_381 G2): a wire point is 256 bytes
  = 4 × 64-byte padded big-endian field elements (x.c0, x.c1, y.c0,
  y.c1), each with a zero 16-byte pad and a 48-byte value < p; the
  point at infinity is 256 zero bytes. MSM inputs additionally require
  the REAL order-n subgroup check (n*P = inf). ADD skips it, matching
  execution-specs bls12_g2_add.

  `blsg2_point_add`/`blsg2_point_dbl` are alias-safe (results staged
  through scratch before the output copy), so the scalar-mul loop runs
  `add(acc, base, acc)` / `dbl(acc, acc)` in place.

  All labels are `blsg2_`-prefixed; shares `blsf_*` staging/constants
  (Bls12Field) and `blsg_*` byte helpers (Bls12G1).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.Programs.Bls12G1

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- G2 data labels WITHOUT a `.section .data` header (pairs with the
    field + G1 fragments). All value cells are LE-limb format. -/
def bls12G2DataFragment : String :=
  ".balign 8\n" ++
  -- p - 2 (Fermat exponent) as 48-byte BIG-endian for MSB-first bit walk
  "blsg2_p_minus_2_be:\n" ++
  "  .byte 0x1a,0x01,0x11,0xea,0x39,0x7f,0xe6,0x9a\n" ++
  "  .byte 0x4b,0x1b,0xa7,0xb6,0x43,0x4b,0xac,0xd7\n" ++
  "  .byte 0x64,0x77,0x4b,0x84,0xf3,0x85,0x12,0xbf\n" ++
  "  .byte 0x67,0x30,0xd2,0xa0,0xf6,0xb0,0xf6,0x24\n" ++
  "  .byte 0x1e,0xab,0xff,0xfe,0xb1,0x53,0xff,0xff\n" ++
  "  .byte 0xb9,0xfe,0xff,0xff,0xff,0xff,0xaa,0xa9\n" ++
  -- p - 1 (negation multiplier), LE limbs
  "blsg2_pm1_le:\n" ++
  "  .quad 0xb9feffffffffaaaa, 0x1eabfffeb153ffff\n" ++
  "  .quad 0x6730d2a0f6b0f624, 0x64774b84f38512bf\n" ++
  "  .quad 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a\n" ++
  -- curve constant b = 4 + 4u as an LE Fp2 element
  "blsg2_b_le:\n" ++
  "  .quad 4, 0, 0, 0, 0, 0\n" ++
  "  .quad 4, 0, 0, 0, 0, 0\n" ++
  -- dynamic Arith384Mod parameter block {a, b, c, module, d}
  "blsg2_fp_params:\n  .zero 40\n" ++
  -- Fp scratch (48 B LE each)
  "blsg2_n:\n  .zero 48\n" ++
  "blsg2_ninv:\n  .zero 48\n" ++
  "blsg2_facc:\n  .zero 48\n" ++
  "blsg2_ft:\n  .zero 48\n" ++
  -- Fp2 scratch (96 B LE each)
  "blsg2_lam:\n  .zero 96\n" ++
  "blsg2_t1:\n  .zero 96\n" ++
  "blsg2_t2:\n  .zero 96\n" ++
  "blsg2_den:\n  .zero 96\n" ++
  "blsg2_inv_out:\n  .zero 96\n" ++
  "blsg2_oc_t:\n  .zero 96\n" ++
  "blsg2_oc_y2:\n  .zero 96\n" ++
  -- affine point working set (192 B LE x || y each)
  "blsg2_pt1:\n  .zero 192\n" ++
  "blsg2_pt2:\n  .zero 192\n" ++
  "blsg2_acc:\n  .zero 192\n" ++
  "blsg2_term:\n  .zero 192\n" ++
  "blsg2_sub_out:\n  .zero 192\n"

/-- Standalone `.data` section for focused probes. -/
def bls12G2DataSection : String :=
  bls12G1DataSection ++ bls12G2DataFragment

/-- Fp d = (a*b) mod p on LE 48-byte cells: a0 = a, a1 = b, a2 = d
    (d may alias an input). Leaf; clobbers t0, a0. -/
def bls12G2FpMulLeFunction : String :=
  "blsg2_fp_mul:\n" ++
  "  la t0, blsg2_fp_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  la a0, blsf_le_zero\n" ++
  "  sd a0, 16(t0)\n" ++
  "  la a0, blsf_le_p\n" ++
  "  sd a0, 24(t0)\n" ++
  "  sd a2, 32(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod\n" ++
  "  ret"

/-- Fp d = (a + b) mod p on LE cells (d = a*1 + b). Leaf; clobbers t0, a0. -/
def bls12G2FpAddLeFunction : String :=
  "blsg2_fp_add:\n" ++
  "  la t0, blsg2_fp_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la a0, blsf_le_one\n" ++
  "  sd a0, 8(t0)\n" ++
  "  sd a1, 16(t0)\n" ++
  "  la a0, blsf_le_p\n" ++
  "  sd a0, 24(t0)\n" ++
  "  sd a2, 32(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod\n" ++
  "  ret"

/-- Fp d = a^(p-2) mod p (Fermat inverse; a reduced, nonzero) on LE
    cells: a0 = a, a1 = d (must NOT alias a or `blsg2_facc`). -/
def bls12G2FpInvFunction : String :=
  "blsg2_fp_inv:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                      # base\n" ++
  "  mv s1, a1                      # result\n" ++
  "  la a0, blsf_le_one\n" ++
  "  la a1, blsg2_facc\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads        # acc = 1\n" ++
  "  li s2, 0                       # exponent byte index\n" ++
  ".Lblsg2_inv_byte:\n" ++
  "  li t0, 48\n" ++
  "  bgeu s2, t0, .Lblsg2_inv_done\n" ++
  "  la t0, blsg2_p_minus_2_be\n" ++
  "  add t0, t0, s2\n" ++
  "  lbu s3, 0(t0)\n" ++
  "  li s4, 128\n" ++
  ".Lblsg2_inv_bit:\n" ++
  "  beqz s4, .Lblsg2_inv_next\n" ++
  "  la a0, blsg2_facc\n" ++
  "  la a1, blsg2_facc\n" ++
  "  la a2, blsg2_facc\n" ++
  "  jal ra, blsg2_fp_mul           # acc = acc^2\n" ++
  "  and t0, s3, s4\n" ++
  "  beqz t0, .Lblsg2_inv_skip\n" ++
  "  la a0, blsg2_facc\n" ++
  "  mv a1, s0\n" ++
  "  la a2, blsg2_facc\n" ++
  "  jal ra, blsg2_fp_mul           # acc *= base\n" ++
  ".Lblsg2_inv_skip:\n" ++
  "  srli s4, s4, 1\n" ++
  "  j .Lblsg2_inv_bit\n" ++
  ".Lblsg2_inv_next:\n" ++
  "  addi s2, s2, 1\n" ++
  "  j .Lblsg2_inv_byte\n" ++
  ".Lblsg2_inv_done:\n" ++
  "  la a0, blsg2_facc\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Fp2 dst += src (96-byte LE buffers). Leaf; clobbers t0, a0. -/
def bls12G2Fp2AddFunction : String :=
  "blsg2_fp2_add:\n" ++
  "  la t0, blsf_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80e52073             # csrs 0x80E, a0 -> Bls12_381ComplexAdd\n" ++
  "  ret"

/-- Fp2 dst -= src. Leaf; clobbers t0, a0. -/
def bls12G2Fp2SubFunction : String :=
  "blsg2_fp2_sub:\n" ++
  "  la t0, blsf_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x80f52073             # csrs 0x80F, a0 -> Bls12_381ComplexSub\n" ++
  "  ret"

/-- Fp2 dst *= src (u^2 = -1). Leaf; clobbers t0, a0. -/
def bls12G2Fp2MulFunction : String :=
  "blsg2_fp2_mul:\n" ++
  "  la t0, blsf_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  mv a0, t0\n" ++
  "  .4byte 0x81052073             # csrs 0x810, a0 -> Bls12_381ComplexMul\n" ++
  "  ret"

/-- Fp2 inverse: a0 = src (96 B LE, nonzero), a1 = dst (must not alias
    src). (c0 + c1 u)^-1 = (c0 - c1 u) / (c0^2 + c1^2). -/
def bls12G2Fp2InvFunction : String :=
  "blsg2_fp2_inv:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s0\n" ++
  "  la a2, blsg2_n\n" ++
  "  jal ra, blsg2_fp_mul           # n = c0^2\n" ++
  "  addi a0, s0, 48\n" ++
  "  addi a1, s0, 48\n" ++
  "  la a2, blsg2_ft\n" ++
  "  jal ra, blsg2_fp_mul           # ft = c1^2\n" ++
  "  la a0, blsg2_n\n" ++
  "  la a1, blsg2_ft\n" ++
  "  la a2, blsg2_n\n" ++
  "  jal ra, blsg2_fp_add           # n = c0^2 + c1^2\n" ++
  "  la a0, blsg2_n\n" ++
  "  la a1, blsg2_ninv\n" ++
  "  jal ra, blsg2_fp_inv\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsg2_ninv\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, blsg2_fp_mul           # dst.c0 = c0 * n^-1\n" ++
  "  addi a0, s0, 48\n" ++
  "  la a1, blsg2_ninv\n" ++
  "  la a2, blsg2_ft\n" ++
  "  jal ra, blsg2_fp_mul           # ft = c1 * n^-1\n" ++
  "  la a0, blsg2_ft\n" ++
  "  la a1, blsg2_pm1_le\n" ++
  "  addi a2, s1, 48\n" ++
  "  jal ra, blsg2_fp_mul           # dst.c1 = -ft\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Copy 192 bytes of 8-aligned LE point data: a0 = src, a1 = dst. -/
def bls12G2Copy192Function : String :=
  "blsg2_copy192:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  li a2, 24\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- Zero 192 bytes at a0 (8-aligned). Leaf; clobbers t0, a0. -/
def blsg2Zero192_prog : Program :=
  [ .LI .x5 (24 : Word),
    .SD .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-12 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G2Zero192Function : String :=
  "blsg2_zero192:\n" ++ emitProgram blsg2Zero192_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsg2Zero192_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G2Zero192Function_eq_prog :
    bls12G2Zero192Function = "blsg2_zero192:\n" ++ emitProgram blsg2Zero192_prog := rfl

#guard bls12G2Zero192Function.startsWith "blsg2_zero192:\n"
#guard blsg2Zero192_prog.length = 6
/-- a0 = 1 iff the two a2-byte buffers at a0/a1 are equal. Leaf. -/
def blsg2EqN_prog : Program :=
  [ .MV .x6 .x10,
    .MV .x7 .x11,
    .MV .x5 .x12,
    .BEQ .x5 .x0 (32 : BitVec 13),
    .LBU .x28 .x6 (0 : BitVec 12),
    .LBU .x29 .x7 (0 : BitVec 12),
    .BNE .x28 .x29 (28 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G2EqNFunction : String :=
  "blsg2_eq_n:\n" ++ emitProgram blsg2EqN_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsg2EqN_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G2EqNFunction_eq_prog :
    bls12G2EqNFunction = "blsg2_eq_n:\n" ++ emitProgram blsg2EqN_prog := rfl

#guard bls12G2EqNFunction.startsWith "blsg2_eq_n:\n"
#guard blsg2EqN_prog.length = 15
/-- Shared chord/tangent tail: with lambda staged at `blsg2_lam`,
    a0 = P, a1 = Q, a2 = out (192 B LE; out may alias P/Q — the result
    is staged through t1/t2 before the output copy):
    x3 = lam^2 - x1 - x2; y3 = lam*(x1 - x3) - y1. -/
def bls12G2ChordTailFunction : String :=
  "blsg2_chord_tail:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_t1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsg2_t1\n" ++
  "  la a1, blsg2_lam\n" ++
  "  jal ra, blsg2_fp2_mul          # t1 = lam^2\n" ++
  "  la a0, blsg2_t1\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blsg2_fp2_sub          # t1 -= x1\n" ++
  "  la a0, blsg2_t1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg2_fp2_sub          # t1 -= x2  (t1 = x3)\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsg2_t2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # t2 = x1\n" ++
  "  la a0, blsg2_t2\n" ++
  "  la a1, blsg2_t1\n" ++
  "  jal ra, blsg2_fp2_sub          # t2 = x1 - x3\n" ++
  "  la a0, blsg2_t2\n" ++
  "  la a1, blsg2_lam\n" ++
  "  jal ra, blsg2_fp2_mul          # t2 *= lam\n" ++
  "  la a0, blsg2_t2\n" ++
  "  addi a1, s0, 96\n" ++
  "  jal ra, blsg2_fp2_sub          # t2 -= y1  (t2 = y3)\n" ++
  "  la a0, blsg2_t1\n" ++
  "  mv a1, s2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsg2_t2\n" ++
  "  addi a1, s2, 96\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Double an affine LE point: a0 = input, a1 = output (192 B LE, may
    alias). Returns a0 = 1 when the result is infinity (input infinity
    or y = 0; output zeroed), else 0. -/
def bls12G2PointDblFunction : String :=
  "blsg2_point_dbl:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  addi a0, s0, 96\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  bnez a0, .Lblsg2_dbl_inf       # y = 0 (covers all-zero infinity)\n" ++
  -- lam = 3x^2 * (2y)^-1
  "  mv a0, s0\n" ++
  "  la a1, blsg2_lam\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # lam = x\n" ++
  "  la a0, blsg2_lam\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blsg2_fp2_mul          # lam = x^2\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_den\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # den = x^2\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_den\n" ++
  "  jal ra, blsg2_fp2_add          # lam = 2x^2\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_den\n" ++
  "  jal ra, blsg2_fp2_add          # lam = 3x^2\n" ++
  "  addi a0, s0, 96\n" ++
  "  la a1, blsg2_den\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # den = y\n" ++
  "  la a0, blsg2_den\n" ++
  "  addi a1, s0, 96\n" ++
  "  jal ra, blsg2_fp2_add          # den = 2y\n" ++
  "  la a0, blsg2_den\n" ++
  "  la a1, blsg2_inv_out\n" ++
  "  jal ra, blsg2_fp2_inv          # inv_out = (2y)^-1\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_inv_out\n" ++
  "  jal ra, blsg2_fp2_mul          # lam = 3x^2 / 2y\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, blsg2_chord_tail\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2_dbl_ret\n" ++
  ".Lblsg2_dbl_inf:\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg2_zero192\n" ++
  "  li a0, 1\n" ++
  ".Lblsg2_dbl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two affine LE points: a0 = P, a1 = Q, a2 = out (192 B LE; out
    may alias). Software-handles infinity, equal-x doubling, and
    P + (-P). Returns a0 = 1 when the result is infinity. -/
def bls12G2PointAddFunction : String :=
  "blsg2_point_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 192\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg2_add_p_finite\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_copy192          # P = inf: result = Q\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 192\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  j .Lblsg2_add_ret\n" ++
  ".Lblsg2_add_p_finite:\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 192\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg2_add_q_finite\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_copy192          # Q = inf: result = P (finite)\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2_add_ret\n" ++
  ".Lblsg2_add_q_finite:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 96\n" ++
  "  jal ra, blsg2_eq_n\n" ++
  "  beqz a0, .Lblsg2_add_distinct_x\n" ++
  "  addi a0, s0, 96\n" ++
  "  addi a1, s1, 96\n" ++
  "  li a2, 96\n" ++
  "  jal ra, blsg2_eq_n\n" ++
  "  beqz a0, .Lblsg2_add_inf       # x equal, y opposite: P + (-P) = inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_point_dbl        # x and y equal: P + P\n" ++
  "  j .Lblsg2_add_ret\n" ++
  ".Lblsg2_add_distinct_x:\n" ++
  -- lam = (y2 - y1) * (x2 - x1)^-1
  "  addi a0, s1, 96\n" ++
  "  la a1, blsg2_lam\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # lam = y2\n" ++
  "  la a0, blsg2_lam\n" ++
  "  addi a1, s0, 96\n" ++
  "  jal ra, blsg2_fp2_sub          # lam = y2 - y1\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blsg2_den\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads        # den = x2\n" ++
  "  la a0, blsg2_den\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, blsg2_fp2_sub          # den = x2 - x1\n" ++
  "  la a0, blsg2_den\n" ++
  "  la a1, blsg2_inv_out\n" ++
  "  jal ra, blsg2_fp2_inv\n" ++
  "  la a0, blsg2_lam\n" ++
  "  la a1, blsg2_inv_out\n" ++
  "  jal ra, blsg2_fp2_mul          # lam = (y2-y1)/(x2-x1)\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, blsg2_chord_tail\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2_add_ret\n" ++
  ".Lblsg2_add_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg2_zero192\n" ++
  "  li a0, 1\n" ++
  ".Lblsg2_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Decode one EIP-2537 G2 wire point (a0 = 256-byte padded BE record,
    byte reads) into a 192-byte LE point at a1: each of the four 64-byte
    field elements needs a zero 16-byte pad and a 48-byte value < p, and
    the point must be all-zero (infinity) or satisfy y^2 = x^3 + 4(u+1).
    Returns a0 = 0 (valid finite), 1 (infinity), or 2 (invalid). -/
def bls12G2DecodeFunction : String :=
  "blsg2_decode_g2:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  li s2, 0                       # felt index 0..3\n" ++
  ".Lblsg2_dec_felt:\n" ++
  "  slli t0, s2, 6\n" ++
  "  add a0, s0, t0\n" ++
  "  li a1, 16\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg2_dec_bad       # pad nonzero\n" ++
  "  slli t0, s2, 6\n" ++
  "  add a0, s0, t0\n" ++
  "  addi a0, a0, 16\n" ++
  "  jal ra, blsg_lt_p\n" ++
  "  beqz a0, .Lblsg2_dec_bad       # value >= p\n" ++
  "  slli t0, s2, 6\n" ++
  "  add a0, s0, t0\n" ++
  "  addi a0, a0, 16\n" ++
  "  slli t0, s2, 4\n" ++
  "  slli t1, s2, 5\n" ++
  "  add t0, t0, t1                 # 48 * felt index\n" ++
  "  add a1, s1, t0\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  addi s2, s2, 1\n" ++
  "  li t0, 4\n" ++
  "  bne s2, t0, .Lblsg2_dec_felt\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 192\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg2_dec_finite\n" ++
  "  li a0, 1                       # all-zero = infinity, valid\n" ++
  "  j .Lblsg2_dec_ret\n" ++
  ".Lblsg2_dec_finite:\n" ++
  -- on-curve: oc_t = x^3 + b; oc_y2 = y^2; equal?
  "  mv a0, s1\n" ++
  "  la a1, blsg2_oc_t\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsg2_oc_t\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg2_fp2_mul          # x^2\n" ++
  "  la a0, blsg2_oc_t\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg2_fp2_mul          # x^3\n" ++
  "  la a0, blsg2_oc_t\n" ++
  "  la a1, blsg2_b_le\n" ++
  "  jal ra, blsg2_fp2_add          # x^3 + (4 + 4u)\n" ++
  "  addi a0, s1, 96\n" ++
  "  la a1, blsg2_oc_y2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsg2_oc_y2\n" ++
  "  addi a1, s1, 96\n" ++
  "  jal ra, blsg2_fp2_mul          # y^2\n" ++
  "  la a0, blsg2_oc_t\n" ++
  "  la a1, blsg2_oc_y2\n" ++
  "  li a2, 96\n" ++
  "  jal ra, blsg2_eq_n\n" ++
  "  beqz a0, .Lblsg2_dec_bad\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2_dec_ret\n" ++
  ".Lblsg2_dec_bad:\n" ++
  "  li a0, 2\n" ++
  ".Lblsg2_dec_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Multiply an affine LE point by a big-endian scalar (MSB-first
    double-and-add over the raw bytes). a0 = scalar bytes, a1 = scalar
    byte length, a2 = base point, a3 = output (192 B LE; must not alias
    the base). Returns a0 = 1 when the result is infinity. -/
def bls12G2ScalarMulFunction : String :=
  "blsg2_scalar_mul:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                      # scalar bytes\n" ++
  "  mv s7, a1                      # scalar byte length\n" ++
  "  mv s1, a2                      # base point\n" ++
  "  mv s2, a3                      # accumulator/output\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg2_zero192\n" ++
  "  li s3, 1                       # accumulator is infinity\n" ++
  "  li s4, 0                       # byte index\n" ++
  ".Lblsg2_mul_byte_loop:\n" ++
  "  bgeu s4, s7, .Lblsg2_mul_done\n" ++
  "  add t0, s0, s4\n" ++
  "  lbu s5, 0(t0)\n" ++
  "  li s6, 128\n" ++
  ".Lblsg2_mul_bit_loop:\n" ++
  "  beqz s6, .Lblsg2_mul_next_byte\n" ++
  "  bnez s3, .Lblsg2_mul_skip_double\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_point_dbl        # alias-safe in-place double\n" ++
  "  mv s3, a0\n" ++
  ".Lblsg2_mul_skip_double:\n" ++
  "  and t0, s5, s6\n" ++
  "  beqz t0, .Lblsg2_mul_advance_bit\n" ++
  "  beqz s3, .Lblsg2_mul_add_base\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_copy192\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 192\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  mv s3, a0                      # base may itself be infinity\n" ++
  "  j .Lblsg2_mul_advance_bit\n" ++
  ".Lblsg2_mul_add_base:\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, blsg2_point_add        # alias-safe in-place add\n" ++
  "  mv s3, a0\n" ++
  ".Lblsg2_mul_advance_bit:\n" ++
  "  srli s6, s6, 1\n" ++
  "  j .Lblsg2_mul_bit_loop\n" ++
  ".Lblsg2_mul_next_byte:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lblsg2_mul_byte_loop\n" ++
  ".Lblsg2_mul_done:\n" ++
  "  mv a0, s3\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- EIP-2537 G2 subgroup check: a0 = LE point. a0 = 1 iff n*P = inf. -/
def bls12G2SubgroupFunction : String :=
  "blsg2_subgroup_g2:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a2, a0\n" ++
  "  la a0, blsg_n_be\n" ++
  "  li a1, 32\n" ++
  "  la a3, blsg2_sub_out\n" ++
  "  jal ra, blsg2_scalar_mul\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- Encode an LE point as the compact 192-byte BE record (4 × 48-byte
    BE felts) at a1; all-zero stays all-zero. -/
def bls12G2EncodeFunction : String :=
  "blsg2_encode:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  li s2, 0\n" ++
  ".Lblsg2_enc_felt:\n" ++
  "  slli t0, s2, 4\n" ++
  "  slli t1, s2, 5\n" ++
  "  add t0, t0, t1                 # 48 * felt index\n" ++
  "  add a0, s0, t0\n" ++
  "  add a1, s1, t0\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  addi s2, s2, 1\n" ++
  "  li t0, 4\n" ++
  "  bne s2, t0, .Lblsg2_enc_felt\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Real BLS12-381 G2 ADD (0x0d) kernel: a0 = pointer to the raw
    512-byte EIP-2537 input (two 256-byte wire points), a1 = 192-byte
    compact BE output. Returns a0 = 0 on success, 1 on invalid input.
    NO subgroup check, per execution-specs bls12_g2_add. -/
def zkvmBls12G2AddRealFunction : String :=
  ".globl zkvm_bls12_g2_add\n" ++
  "zkvm_bls12_g2_add:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la a1, blsg2_pt1\n" ++
  "  jal ra, blsg2_decode_g2\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg2add_invalid\n" ++
  "  addi a0, s0, 256\n" ++
  "  la a1, blsg2_pt2\n" ++
  "  jal ra, blsg2_decode_g2\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg2add_invalid\n" ++
  "  la a0, blsg2_pt1\n" ++
  "  la a1, blsg2_pt2\n" ++
  "  la a2, blsg2_pt1\n" ++
  "  jal ra, blsg2_point_add\n" ++
  "  la a0, blsg2_pt1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg2_encode\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2add_ret\n" ++
  ".Lblsg2add_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblsg2add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Real BLS12-381 G2 MSM (0x0e) kernel: a0 = pointer to the raw
    EIP-2537 input (k pairs of 256-byte wire point + 32-byte BE scalar,
    288-byte stride), a1 = pair count k (>= 1, length pre-gated),
    a2 = 192-byte compact BE output. Every input point must decode AND
    pass the order-n subgroup check. Returns a0 = 0 / 1 invalid. -/
def zkvmBls12G2MsmRealFunction : String :=
  ".globl zkvm_bls12_g2_msm\n" ++
  "zkvm_bls12_g2_msm:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0                      # input cursor\n" ++
  "  mv s1, a1                      # remaining pairs\n" ++
  "  mv s2, a2                      # output\n" ++
  "  la a0, blsg2_acc\n" ++
  "  jal ra, blsg2_zero192\n" ++
  ".Lblsg2msm_pair:\n" ++
  "  beqz s1, .Lblsg2msm_done\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsg2_pt1\n" ++
  "  jal ra, blsg2_decode_g2\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg2msm_invalid\n" ++
  "  la a0, blsg2_pt1\n" ++
  "  jal ra, blsg2_subgroup_g2\n" ++
  "  beqz a0, .Lblsg2msm_invalid    # P not in the order-n subgroup\n" ++
  "  addi a0, s0, 256               # 32-byte BE scalar\n" ++
  "  li a1, 32\n" ++
  "  la a2, blsg2_pt1\n" ++
  "  la a3, blsg2_term\n" ++
  "  jal ra, blsg2_scalar_mul\n" ++
  "  la a0, blsg2_acc\n" ++
  "  la a1, blsg2_term\n" ++
  "  la a2, blsg2_acc\n" ++
  "  jal ra, blsg2_point_add\n" ++
  "  addi s0, s0, 288\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lblsg2msm_pair\n" ++
  ".Lblsg2msm_done:\n" ++
  "  la a0, blsg2_acc\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg2_encode\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg2msm_ret\n" ++
  ".Lblsg2msm_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblsg2msm_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- The full self-contained G2 suite. Pairs with the field + G1 + G2
    data fragments; requires the G1 byte helpers (`blsg_*`) and
    `blsf_copy_quads` to be linked alongside (the G1 suite provides the
    former; Bls12Field's copy helper is included here). -/
def bls12G2PrecompileFunctions : String :=
  bls12G2FpMulLeFunction ++ "\n" ++
  bls12G2FpAddLeFunction ++ "\n" ++
  bls12G2FpInvFunction ++ "\n" ++
  bls12G2Fp2AddFunction ++ "\n" ++
  bls12G2Fp2SubFunction ++ "\n" ++
  bls12G2Fp2MulFunction ++ "\n" ++
  bls12G2Fp2InvFunction ++ "\n" ++
  bls12G2Copy192Function ++ "\n" ++
  bls12G2Zero192Function ++ "\n" ++
  bls12G2EqNFunction ++ "\n" ++
  bls12G2ChordTailFunction ++ "\n" ++
  bls12G2PointDblFunction ++ "\n" ++
  bls12G2PointAddFunction ++ "\n" ++
  bls12G2DecodeFunction ++ "\n" ++
  bls12G2ScalarMulFunction ++ "\n" ++
  bls12G2SubgroupFunction ++ "\n" ++
  bls12G2EncodeFunction ++ "\n" ++
  zkvmBls12G2AddRealFunction ++ "\n" ++
  zkvmBls12G2MsmRealFunction

/-- Probe for the real G2 ADD kernel: raw 512-byte EIP-2537 input at
    `0x40000008`; status at OUTPUT+0, 192-byte compact result at +8. -/
def ziskBls12G2AddRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_g2_add\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblsg2_add_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  ".Lblsg2_add_probe_done:"

def ziskBls12G2AddRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G2AddRealProbePrologue
  dataAsm     := bls12G2DataSection
}

/-- Probe for the real G2 MSM kernel: pair count (u64) at `0x40000008`,
    raw pairs from `0x40000010`; status at OUTPUT+0, result at +8. -/
def ziskBls12G2MsmRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000008\n" ++
  "  ld a1, 0(t0)\n" ++
  "  addi a0, t0, 8\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_g2_msm\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblsg2_msm_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  bls12G2PrecompileFunctions ++ "\n" ++
  ".Lblsg2_msm_probe_done:"

def ziskBls12G2MsmRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G2MsmRealProbePrologue
  dataAsm     := bls12G2DataSection
}

end EvmAsm.Codegen
