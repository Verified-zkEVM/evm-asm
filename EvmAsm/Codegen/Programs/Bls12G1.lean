/-
  EvmAsm.Codegen.Programs.Bls12G1

  Affine BLS12-381 G1 curve helpers plus the runtime EIP-2537 precompile
  kernels `zkvm_bls12_g1_add` (0x0b) and `zkvm_bls12_g1_msm` (0x0c).

  Internal points are COMPACT 96-byte big-endian affine records x || y
  (48-byte coordinates); the point at infinity is encoded as 96 zero
  bytes. The kernels take the RAW EIP-2537 wire input (a pointer into
  EVM memory; every read is byte-wise so alignment is free): each wire
  point is 128 bytes — two 64-byte field elements whose top 16 bytes
  MUST be zero and whose 48-byte value must be < p (execution-specs
  `bytes_to_fq` + padding rule), decoded by `blsg_decode_g1`.

  `blsg_point_add` / `blsg_point_dbl` are backed by the ziskemu
  Bls12_381CurveAdd/Dbl accelerators (`csrs 0x80C` / `csrs 0x80D`,
  pre-encoded `.4byte`s, verified by scripts/codegen-zisk-bls12-accel-
  check.sh). The affine special cases the accelerators exclude (inputs
  at infinity, doubling with y = 0, adding points with equal x) stay in
  software — the same wrapper shape as Bn254Curve/Secp256k1Curve.

  Unlike BN254, the G1 cofactor is NOT 1 (h = 0x396c8c005555e1568c00aaab0000aaab),
  so EIP-2537 requires a REAL subgroup check for MSM inputs:
  `blsg_subgroup_g1` checks n*P = inf by double-and-add over the group
  order n. ADD (0x0b) deliberately skips the subgroup check, matching
  execution-specs `bls12_g1_add`.

  All labels are `blsg_`-prefixed; the LE staging points + parameter
  blocks (`blsf_p1`/`blsf_p2`/`blsf_curve_params`) and the Arith384Mod
  cells come from `Bls12Field.lean`'s data fragment.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Bls12Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- BLS12-381 G1 curve data labels WITHOUT a `.section .data` header
    (pairs with `bls12FieldDataFragment`). -/
def bls12G1DataFragment : String :=
  ".balign 8\n" ++
  -- p as 48-byte big-endian (the wire-side coordinate range check)
  "blsg_p_be:\n" ++
  "  .byte 0x1a,0x01,0x11,0xea,0x39,0x7f,0xe6,0x9a\n" ++
  "  .byte 0x4b,0x1b,0xa7,0xb6,0x43,0x4b,0xac,0xd7\n" ++
  "  .byte 0x64,0x77,0x4b,0x84,0xf3,0x85,0x12,0xbf\n" ++
  "  .byte 0x67,0x30,0xd2,0xa0,0xf6,0xb0,0xf6,0x24\n" ++
  "  .byte 0x1e,0xab,0xff,0xfe,0xb1,0x53,0xff,0xff\n" ++
  "  .byte 0xb9,0xfe,0xff,0xff,0xff,0xff,0xaa,0xab\n" ++
  -- curve constant b = 4 (y^2 = x^3 + 4) as a 48-byte BE field element
  "blsg_b_be:\n" ++
  "  .zero 47\n" ++
  "  .byte 0x04\n" ++
  -- group order n (the subgroup-check scalar), 32-byte BE
  "blsg_n_be:\n" ++
  "  .byte 0x73,0xed,0xa7,0x53,0x29,0x9d,0x7d,0x48\n" ++
  "  .byte 0x33,0x39,0xd8,0x08,0x09,0xa1,0xd8,0x05\n" ++
  "  .byte 0x53,0xbd,0xa4,0x02,0xff,0xfe,0x5b,0xfe\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x01\n" ++
  -- on-curve scratch: t = x^2 / x^3, rhs = x^3 + 4, y2 = y^2
  ".balign 8\n" ++
  "blsg_t:\n  .zero 48\n" ++
  "blsg_rhs:\n  .zero 48\n" ++
  "blsg_y2:\n  .zero 48\n" ++
  -- compact decoded operands + working buffers
  ".balign 8\n" ++
  "blsg_pt1:\n  .zero 96\n" ++
  "blsg_pt2:\n  .zero 96\n" ++
  "blsg_pt_tmp:\n  .zero 96\n" ++   -- scalar_mul / point_add result staging
  "blsg_acc96:\n  .zero 96\n" ++    -- MSM accumulator
  "blsg_term96:\n  .zero 96\n" ++   -- MSM per-pair k_i * P_i
  "blsg_sub_out:\n  .zero 96\n"     -- subgroup-check n*P output

/-- Standalone `.data` section (field + G1 curve) for focused probes. -/
def bls12G1DataSection : String :=
  bls12FieldDataSection ++ bls12G1DataFragment

/-- Convert a 48-byte big-endian buffer (`a0`, any alignment) into six
    little-endian u64 limbs (`a1`, 8-aligned), LSB limb first. Leaf. -/
def bls12G1BeToLeFunction : String :=
  "blsg_be_to_le:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lblsg_b2l_quad:\n" ++
  "  li t1, 40\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a0, t1             # BE offset of the limb's MSB\n" ++
  "  li t3, 0\n" ++
  "  li t4, 8\n" ++
  ".Lblsg_b2l_byte:\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  or t3, t3, t5\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lblsg_b2l_byte\n" ++
  "  slli t2, t0, 3\n" ++
  "  add t2, a1, t2\n" ++
  "  sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 6\n" ++
  "  bne t0, t1, .Lblsg_b2l_quad\n" ++
  "  ret"

/-- Convert six little-endian u64 limbs (`a0`, 8-aligned) into a 48-byte
    big-endian buffer (`a1`, any alignment). Inverse of `blsg_be_to_le`. -/
def bls12G1LeToBeFunction : String :=
  "blsg_le_to_be:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lblsg_l2b_quad:\n" ++
  "  slli t1, t0, 3\n" ++
  "  add t2, a0, t1\n" ++
  "  ld t3, 0(t2)\n" ++
  "  li t1, 47\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a1, t1             # BE offset of the limb's LSB\n" ++
  "  li t4, 8\n" ++
  ".Lblsg_l2b_byte:\n" ++
  "  andi t5, t3, 0xff\n" ++
  "  sb t5, 0(t1)\n" ++
  "  srli t3, t3, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lblsg_l2b_byte\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 6\n" ++
  "  bne t0, t1, .Lblsg_l2b_quad\n" ++
  "  ret"

/-- a0 = 1 iff the a1 bytes at a0 are all zero. Leaf. -/
def bls12G1IsZeroFunction : String :=
  "blsg_is_zero_n:\n" ++
  "  mv t1, a0\n" ++
  "  mv t0, a1\n" ++
  ".Lblsg_iz_loop:\n" ++
  "  beqz t0, .Lblsg_iz_yes\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  bnez t2, .Lblsg_iz_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lblsg_iz_loop\n" ++
  ".Lblsg_iz_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lblsg_iz_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- a0 = 1 iff the two 48-byte buffers at a0 / a1 are equal. Leaf. -/
def bls12G1Eq48Function : String :=
  "blsg_eq48:\n" ++
  "  li t0, 48\n" ++
  "  mv t1, a0\n" ++
  "  mv t2, a1\n" ++
  ".Lblsg_eq_loop:\n" ++
  "  beqz t0, .Lblsg_eq_yes\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lblsg_eq_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lblsg_eq_loop\n" ++
  ".Lblsg_eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lblsg_eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- a0 = 1 iff the 48-byte big-endian integer at a0 is `< p`. Leaf. -/
def bls12G1LtPFunction : String :=
  "blsg_lt_p:\n" ++
  "  la t0, blsg_p_be\n" ++
  "  li t1, 48\n" ++
  "  mv t2, a0\n" ++
  ".Lblsg_ltp_loop:\n" ++
  "  beqz t1, .Lblsg_ltp_no      # equal => not less\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lblsg_ltp_yes\n" ++
  "  bltu t4, t3, .Lblsg_ltp_no\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lblsg_ltp_loop\n" ++
  ".Lblsg_ltp_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lblsg_ltp_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- Copy 96 bytes from a0 to a1 (byte loop; alignment-free). -/
def bls12G1Copy96Function : String :=
  "blsg_copy96:\n" ++
  "  li t0, 96\n" ++
  ".Lblsg_copy96_loop:\n" ++
  "  beqz t0, .Lblsg_copy96_ret\n" ++
  "  lbu t1, 0(a0)\n" ++
  "  sb t1, 0(a1)\n" ++
  "  addi a0, a0, 1\n" ++
  "  addi a1, a1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lblsg_copy96_loop\n" ++
  ".Lblsg_copy96_ret:\n" ++
  "  ret"

/-- Zero 96 bytes at a0 (byte loop; alignment-free). -/
def bls12G1Zero96Function : String :=
  "blsg_zero96:\n" ++
  "  li t0, 96\n" ++
  ".Lblsg_zero96_loop:\n" ++
  "  beqz t0, .Lblsg_zero96_ret\n" ++
  "  sb zero, 0(a0)\n" ++
  "  addi a0, a0, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lblsg_zero96_loop\n" ++
  ".Lblsg_zero96_ret:\n" ++
  "  ret"

/-- Fp d = (a*b) mod p: a0/a1 = 48-byte BE inputs, a2 = 48-byte BE
    output, via the Arith384Mod `blsf_mul_params` block. -/
def bls12G1MulModPFunction : String :=
  "blsg_mul_mod_p:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, blsf_le_a\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_le_b\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  la a0, blsf_mul_params\n" ++
  "  .4byte 0x80b52073           # csrs 0x80B, a0 -> Arith384Mod\n" ++
  "  la a0, blsf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Fp d = (a + b) mod p: same surface via `blsf_add_params`
    (`d = a*1 + b`). -/
def bls12G1AddModPFunction : String :=
  "blsg_add_mod_p:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, blsf_le_a\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_le_b\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  la a0, blsf_add_params\n" ++
  "  .4byte 0x80b52073           # csrs 0x80B, a0 -> Arith384Mod\n" ++
  "  la a0, blsf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Double an affine point. a0 = input x||y (compact BE 96), a1 = output.
    Returns a0 = 1 when the result is infinity (y = 0 input, which also
    covers the (0,0) infinity encoding), output zeroed; else 0. -/
def bls12G1PointDblFunction : String :=
  "blsg_point_dbl:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  addi a0, s0, 48\n" ++
  "  li a1, 48\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_dbl_finite\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li a0, 1\n" ++
  "  j .Lblsg_dbl_ret\n" ++
  ".Lblsg_dbl_finite:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  jal ra, blsg_be_to_le          # p1.x\n" ++
  "  addi a0, s0, 48\n" ++
  "  la a1, blsf_p1\n" ++
  "  addi a1, a1, 48\n" ++
  "  jal ra, blsg_be_to_le          # p1.y\n" ++
  "  la a0, blsf_p1\n" ++
  "  .4byte 0x80d52073              # csrs 0x80D, a0 -> Bls12_381CurveDbl\n" ++
  "  la a0, blsf_p1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg_le_to_be          # out.x\n" ++
  "  la a0, blsf_p1\n" ++
  "  addi a0, a0, 48\n" ++
  "  addi a1, s1, 48\n" ++
  "  jal ra, blsg_le_to_be          # out.y\n" ++
  "  li a0, 0\n" ++
  ".Lblsg_dbl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two affine points. a0 = P, a1 = Q, a2 = out (all compact BE 96,
    infinity = all-zero). Software-handles the accelerator-excluded
    cases: P or Q at infinity, equal x with equal y (doubling), equal x
    with opposite y (infinity). Returns a0 = 1 when the result is
    infinity (output zeroed), else 0. -/
def bls12G1PointAddFunction : String :=
  "blsg_point_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_add_p_finite\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96            # P = inf: result = Q\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  j .Lblsg_add_ret\n" ++
  ".Lblsg_add_p_finite:\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_add_q_finite\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96            # Q = inf: result = P (finite)\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_add_ret\n" ++
  ".Lblsg_add_q_finite:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg_eq48\n" ++
  "  beqz a0, .Lblsg_add_distinct_x\n" ++
  "  addi a0, s0, 48\n" ++
  "  addi a1, s1, 48\n" ++
  "  jal ra, blsg_eq48\n" ++
  "  beqz a0, .Lblsg_add_inf        # x equal, y opposite: P + (-P) = inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_point_dbl         # x and y equal: P + P\n" ++
  "  j .Lblsg_add_ret\n" ++
  ".Lblsg_add_distinct_x:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  jal ra, blsg_be_to_le          # p1.x\n" ++
  "  addi a0, s0, 48\n" ++
  "  la a1, blsf_p1\n" ++
  "  addi a1, a1, 48\n" ++
  "  jal ra, blsg_be_to_le          # p1.y\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blsf_p2\n" ++
  "  jal ra, blsg_be_to_le          # p2.x\n" ++
  "  addi a0, s1, 48\n" ++
  "  la a1, blsf_p2\n" ++
  "  addi a1, a1, 48\n" ++
  "  jal ra, blsg_be_to_le          # p2.y\n" ++
  "  la a0, blsf_curve_params\n" ++
  "  .4byte 0x80c52073              # csrs 0x80C, a0 -> Bls12_381CurveAdd\n" ++
  "  la a0, blsf_p1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_le_to_be          # out.x\n" ++
  "  la a0, blsf_p1\n" ++
  "  addi a0, a0, 48\n" ++
  "  addi a1, s2, 48\n" ++
  "  jal ra, blsg_le_to_be          # out.y\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_add_ret\n" ++
  ".Lblsg_add_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li a0, 1\n" ++
  ".Lblsg_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- a0 = 1 iff the finite point at a0 (coords already `< p`) satisfies
    y^2 = x^3 + 4 mod p. -/
def bls12G1OnCurveFunction : String :=
  "blsg_on_curve:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv a1, s0\n" ++
  "  la a2, blsg_t\n" ++
  "  jal ra, blsg_mul_mod_p         # t = x^2\n" ++
  "  la a0, blsg_t\n" ++
  "  mv a1, s0\n" ++
  "  la a2, blsg_t\n" ++
  "  jal ra, blsg_mul_mod_p         # t = x^3\n" ++
  "  la a0, blsg_t\n" ++
  "  la a1, blsg_b_be\n" ++
  "  la a2, blsg_rhs\n" ++
  "  jal ra, blsg_add_mod_p         # rhs = x^3 + 4\n" ++
  "  addi a0, s0, 48\n" ++
  "  addi a1, s0, 48\n" ++
  "  la a2, blsg_y2\n" ++
  "  jal ra, blsg_mul_mod_p         # y2 = y^2\n" ++
  "  la a0, blsg_rhs\n" ++
  "  la a1, blsg_y2\n" ++
  "  jal ra, blsg_eq48\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

/-- Decode one EIP-2537 G1 wire point (a0 = 128-byte padded BE record)
    into a compact 96-byte point at a1: each 64-byte field element must
    have its 16 pad bytes zero and 48-byte value < p, and the point must
    be (0,0) (infinity) or on the curve. Returns a0 = 0 (valid finite),
    1 ((0,0) infinity), or 2 (invalid encoding / off-curve). -/
def bls12G1DecodeFunction : String :=
  "blsg_decode_g1:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 16\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_dec_bad        # x pad nonzero\n" ++
  "  addi a0, s0, 64\n" ++
  "  li a1, 16\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_dec_bad        # y pad nonzero\n" ++
  -- compact copy: x bytes [16..64) -> out[0..48), y [80..128) -> out[48..96)
  "  addi t1, s0, 16\n" ++
  "  mv t2, s1\n" ++
  "  li t0, 48\n" ++
  ".Lblsg_dec_cx:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t2)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lblsg_dec_cx\n" ++
  "  addi t1, s0, 80\n" ++
  "  addi t2, s1, 48\n" ++
  "  li t0, 48\n" ++
  ".Lblsg_dec_cy:\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  sb t3, 0(t2)\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  bnez t0, .Lblsg_dec_cy\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_lt_p\n" ++
  "  beqz a0, .Lblsg_dec_bad        # x >= p\n" ++
  "  addi a0, s1, 48\n" ++
  "  jal ra, blsg_lt_p\n" ++
  "  beqz a0, .Lblsg_dec_bad        # y >= p\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_dec_finite\n" ++
  "  li a0, 1                       # (0,0) = infinity, valid\n" ++
  "  j .Lblsg_dec_ret\n" ++
  ".Lblsg_dec_finite:\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_on_curve\n" ++
  "  beqz a0, .Lblsg_dec_bad\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_dec_ret\n" ++
  ".Lblsg_dec_bad:\n" ++
  "  li a0, 2\n" ++
  ".Lblsg_dec_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Multiply an affine point by a big-endian scalar (MSB-first
    double-and-add over the raw bytes, matching py_ecc `multiply`).
    a0 = scalar bytes, a1 = scalar byte length, a2 = base x||y,
    a3 = output x||y (all compact BE). Returns a0 = 1 when the result
    is infinity (output zeroed). -/
def bls12G1ScalarMulFunction : String :=
  "blsg_scalar_mul:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                      # scalar bytes\n" ++
  "  mv s7, a1                      # scalar byte length\n" ++
  "  mv s1, a2                      # base point\n" ++
  "  mv s2, a3                      # accumulator/output\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li s3, 1                       # accumulator is infinity\n" ++
  "  li s4, 0                       # byte index\n" ++
  ".Lblsg_mul_byte_loop:\n" ++
  "  bgeu s4, s7, .Lblsg_mul_done\n" ++
  "  add t0, s0, s4\n" ++
  "  lbu s5, 0(t0)\n" ++
  "  li s6, 128\n" ++
  ".Lblsg_mul_bit_loop:\n" ++
  "  beqz s6, .Lblsg_mul_next_byte\n" ++
  "  bnez s3, .Lblsg_mul_skip_double\n" ++
  "  mv a0, s2\n" ++
  "  la a1, blsg_pt_tmp\n" ++
  "  jal ra, blsg_point_dbl\n" ++
  "  mv s3, a0\n" ++
  "  la a0, blsg_pt_tmp\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96\n" ++
  ".Lblsg_mul_skip_double:\n" ++
  "  and t0, s5, s6\n" ++
  "  beqz t0, .Lblsg_mul_advance_bit\n" ++
  "  beqz s3, .Lblsg_mul_add_base\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  mv s3, a0                      # base may itself be (0,0)\n" ++
  "  j .Lblsg_mul_advance_bit\n" ++
  ".Lblsg_mul_add_base:\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s1\n" ++
  "  la a2, blsg_pt_tmp\n" ++
  "  jal ra, blsg_point_add\n" ++
  "  mv s3, a0\n" ++
  "  la a0, blsg_pt_tmp\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96\n" ++
  ".Lblsg_mul_advance_bit:\n" ++
  "  srli s6, s6, 1\n" ++
  "  j .Lblsg_mul_bit_loop\n" ++
  ".Lblsg_mul_next_byte:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lblsg_mul_byte_loop\n" ++
  ".Lblsg_mul_done:\n" ++
  "  mv a0, s3\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- EIP-2537 G1 subgroup check: a0 = compact point. Returns a0 = 1 iff
    n*P = inf (P in the order-n subgroup; infinity passes trivially).
    The G1 cofactor is not 1, so this is a REAL check, unlike BN254. -/
def bls12G1SubgroupFunction : String :=
  "blsg_subgroup_g1:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp)\n" ++
  "  mv a2, a0\n" ++
  "  la a0, blsg_n_be\n" ++
  "  li a1, 32\n" ++
  "  la a3, blsg_sub_out\n" ++
  "  jal ra, blsg_scalar_mul\n" ++
  "  ld ra, 0(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret                            # scalar_mul already returns the inf flag"

/-- Real BLS12-381 G1 ADD (0x0b) kernel: a0 = pointer to the raw
    256-byte EIP-2537 input (two 128-byte wire points; byte reads, so
    EVM-memory alignment is free), a1 = 96-byte compact BE output.
    Returns a0 = 0 on success, 1 on invalid input (bad padding,
    coordinate >= p, or off-curve — execution-specs InvalidParameter ->
    failed call). NO subgroup check, per execution-specs bls12_g1_add. -/
def zkvmBls12G1AddRealFunction : String :=
  ".globl zkvm_bls12_g1_add\n" ++
  "zkvm_bls12_g1_add:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0; mv s1, a1\n" ++
  "  la a1, blsg_pt1\n" ++
  "  jal ra, blsg_decode_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg1add_invalid\n" ++
  "  addi a0, s0, 128\n" ++
  "  la a1, blsg_pt2\n" ++
  "  jal ra, blsg_decode_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg1add_invalid\n" ++
  "  la a0, blsg_pt1\n" ++
  "  la a1, blsg_pt2\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, blsg_point_add\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg1add_ret\n" ++
  ".Lblsg1add_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblsg1add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Real BLS12-381 G1 MSM (0x0c) kernel: a0 = pointer to the raw
    EIP-2537 input (k pairs of 128-byte wire point + 32-byte BE scalar,
    160-byte stride), a1 = pair count k (>= 1, length pre-gated),
    a2 = 96-byte compact BE output. Each input point must decode AND
    pass the order-n subgroup check (EIP-2537 MSM rule). Returns
    a0 = 0 on success, 1 on invalid input. -/
def zkvmBls12G1MsmRealFunction : String :=
  ".globl zkvm_bls12_g1_msm\n" ++
  "zkvm_bls12_g1_msm:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0                      # input cursor\n" ++
  "  mv s1, a1                      # remaining pairs\n" ++
  "  mv s2, a2                      # output\n" ++
  "  la a0, blsg_acc96\n" ++
  "  jal ra, blsg_zero96\n" ++
  ".Lblsg1msm_pair:\n" ++
  "  beqz s1, .Lblsg1msm_done\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsg_pt1\n" ++
  "  jal ra, blsg_decode_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lblsg1msm_invalid\n" ++
  "  la a0, blsg_pt1\n" ++
  "  jal ra, blsg_subgroup_g1\n" ++
  "  beqz a0, .Lblsg1msm_invalid    # P not in the order-n subgroup\n" ++
  "  addi a0, s0, 128               # 32-byte BE scalar\n" ++
  "  li a1, 32\n" ++
  "  la a2, blsg_pt1\n" ++
  "  la a3, blsg_term96\n" ++
  "  jal ra, blsg_scalar_mul\n" ++
  "  la a0, blsg_acc96\n" ++
  "  la a1, blsg_term96\n" ++
  "  la a2, blsg_pt_tmp\n" ++
  "  jal ra, blsg_point_add\n" ++
  "  la a0, blsg_pt_tmp\n" ++
  "  la a1, blsg_acc96\n" ++
  "  jal ra, blsg_copy96\n" ++
  "  addi s0, s0, 160\n" ++
  "  addi s1, s1, -1\n" ++
  "  j .Lblsg1msm_pair\n" ++
  ".Lblsg1msm_done:\n" ++
  "  la a0, blsg_acc96\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg1msm_ret\n" ++
  ".Lblsg1msm_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lblsg1msm_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- The full self-contained BLS12-381 G1 suite (field conversions +
    curve helpers + the two real kernels). Pairs with
    `bls12FieldDataFragment ++ bls12G1DataFragment` in the data section. -/
def bls12G1PrecompileFunctions : String :=
  bls12G1BeToLeFunction ++ "\n" ++
  bls12G1LeToBeFunction ++ "\n" ++
  bls12G1IsZeroFunction ++ "\n" ++
  bls12G1Eq48Function ++ "\n" ++
  bls12G1LtPFunction ++ "\n" ++
  bls12G1Copy96Function ++ "\n" ++
  bls12G1Zero96Function ++ "\n" ++
  bls12G1MulModPFunction ++ "\n" ++
  bls12G1AddModPFunction ++ "\n" ++
  bls12G1PointDblFunction ++ "\n" ++
  bls12G1PointAddFunction ++ "\n" ++
  bls12G1OnCurveFunction ++ "\n" ++
  bls12G1DecodeFunction ++ "\n" ++
  bls12G1ScalarMulFunction ++ "\n" ++
  bls12G1SubgroupFunction ++ "\n" ++
  zkvmBls12G1AddRealFunction ++ "\n" ++
  zkvmBls12G1MsmRealFunction

/-- Probe for the real G1 ADD kernel: raw 256-byte EIP-2537 input at
    `0x40000008`; writes status (u64) at OUTPUT+0 and the 96-byte
    compact result at OUTPUT+8. -/
def ziskBls12G1AddRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a0, 0x40000008\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_g1_add\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblsg1_add_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  ".Lblsg1_add_probe_done:"

def ziskBls12G1AddRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G1AddRealProbePrologue
  dataAsm     := bls12G1DataSection
}

/-- Probe for the real G1 MSM kernel: pair count (u64) at `0x40000008`,
    raw pairs from `0x40000010`; writes status at OUTPUT+0 and the
    96-byte compact result at OUTPUT+8. -/
def ziskBls12G1MsmRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t0, 0x40000008\n" ++
  "  ld a1, 0(t0)\n" ++
  "  addi a0, t0, 8\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bls12_g1_msm\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lblsg1_msm_probe_done\n" ++
  bls12G1PrecompileFunctions ++ "\n" ++
  ".Lblsg1_msm_probe_done:"

def ziskBls12G1MsmRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBls12G1MsmRealProbePrologue
  dataAsm     := bls12G1DataSection
}

end EvmAsm.Codegen
