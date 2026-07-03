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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
  "blsg_sub_out:\n  .zero 96\n" ++  -- subgroup-check n*P output
  -- LE-internal scalar-mul working set (the BE<->LE conversion happens
  -- once per scalar mul, not once per point op)
  "blsg_le_base:\n  .zero 96\n" ++
  "blsg_le_acc:\n  .zero 96\n"

/-- Standalone `.data` section (field + G1 curve) for focused probes. -/
def bls12G1DataSection : String :=
  bls12FieldDataSection ++ bls12G1DataFragment

/-- Convert a 48-byte big-endian buffer (`a0`, any alignment) into six
    little-endian u64 limbs (`a1`, 8-aligned), LSB limb first. Leaf. -/
def blsgBeToLe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (40 : Word),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .SUB .x6 .x6 .x7,
    .ADD .x6 .x10 .x6,
    .LI .x28 (0 : Word),
    .LI .x29 (8 : Word),
    .SLLI .x28 .x28 (8 : BitVec 6),
    .LBU .x30 .x6 (0 : BitVec 12),
    .OR .x28 .x28 .x30,
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-20 : BitVec 13),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .ADD .x7 .x11 .x7,
    .SD .x7 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x6 (6 : Word),
    .BNE .x5 .x6 (-68 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1BeToLeFunction : String :=
  "blsg_be_to_le:\n" ++ emitProgram blsgBeToLe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgBeToLe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1BeToLeFunction_eq_prog :
    bls12G1BeToLeFunction = "blsg_be_to_le:\n" ++ emitProgram blsgBeToLe_prog := rfl

#guard bls12G1BeToLeFunction.startsWith "blsg_be_to_le:\n"
#guard blsgBeToLe_prog.length = 20
/-- Convert six little-endian u64 limbs (`a0`, 8-aligned) into a 48-byte
    big-endian buffer (`a1`, any alignment). Inverse of `blsg_be_to_le`. -/
def blsgLeToBe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .SLLI .x6 .x5 (3 : BitVec 6),
    .ADD .x7 .x10 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LI .x6 (47 : Word),
    .SLLI .x7 .x5 (3 : BitVec 6),
    .SUB .x6 .x6 .x7,
    .ADD .x6 .x11 .x6,
    .LI .x29 (8 : Word),
    .ANDI .x30 .x28 (255 : BitVec 12),
    .SB .x6 .x30 (0 : BitVec 12),
    .SRLI .x28 .x28 (8 : BitVec 6),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .ADDI .x29 .x29 (-1 : BitVec 12),
    .BNE .x29 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .LI .x6 (6 : Word),
    .BNE .x5 .x6 (-64 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1LeToBeFunction : String :=
  "blsg_le_to_be:\n" ++ emitProgram blsgLeToBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgLeToBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1LeToBeFunction_eq_prog :
    bls12G1LeToBeFunction = "blsg_le_to_be:\n" ++ emitProgram blsgLeToBe_prog := rfl

#guard bls12G1LeToBeFunction.startsWith "blsg_le_to_be:\n"
#guard blsgLeToBe_prog.length = 19
/-- a0 = 1 iff the a1 bytes at a0 are all zero. Leaf. -/
def blsgIsZeroN_prog : Program :=
  [ .MV .x6 .x10,
    .MV .x5 .x11,
    .BEQ .x5 .x0 (24 : BitVec 13),
    .LBU .x7 .x6 (0 : BitVec 12),
    .BNE .x7 .x0 (24 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1IsZeroFunction : String :=
  "blsg_is_zero_n:\n" ++ emitProgram blsgIsZeroN_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgIsZeroN_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1IsZeroFunction_eq_prog :
    bls12G1IsZeroFunction = "blsg_is_zero_n:\n" ++ emitProgram blsgIsZeroN_prog := rfl

#guard bls12G1IsZeroFunction.startsWith "blsg_is_zero_n:\n"
#guard blsgIsZeroN_prog.length = 12
/-- a0 = 1 iff the two 48-byte buffers at a0 / a1 are equal. Leaf. -/
def blsgEq48_prog : Program :=
  [ .LI .x5 (48 : Word),
    .MV .x6 .x10,
    .MV .x7 .x11,
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

def bls12G1Eq48Function : String :=
  "blsg_eq48:\n" ++ emitProgram blsgEq48_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgEq48_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1Eq48Function_eq_prog :
    bls12G1Eq48Function = "blsg_eq48:\n" ++ emitProgram blsgEq48_prog := rfl

#guard bls12G1Eq48Function.startsWith "blsg_eq48:\n"
#guard blsgEq48_prog.length = 15
/-- a0 = 1 iff the 48-byte big-endian integer at a0 is `< p`. Leaf. -/
def blsgLtP_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsg_p_be (GuestAddrs.blsg_lt_p + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsg_p_be (GuestAddrs.blsg_lt_p + 0)),
    .LI .x6 (48 : Word),
    .MV .x7 .x10,
    .BEQ .x6 .x0 (44 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .LBU .x29 .x5 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (28 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1LtPFunction : String :=
  "blsg_lt_p:\n" ++ emitProgram blsgLtP_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgLtP_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1LtPFunction_eq_prog :
    bls12G1LtPFunction = "blsg_lt_p:\n" ++ emitProgram blsgLtP_prog := rfl

#guard bls12G1LtPFunction.startsWith "blsg_lt_p:\n"
#guard blsgLtP_prog.length = 17
/-- Copy 96 bytes from a0 to a1 (quad loop; every call site — frame
    lanes, probe OUTPUT+8, the `.data` point cells — is 8-aligned). -/
def blsgCopy96_prog : Program :=
  [ .LI .x5 (12 : Word),
    .LD .x6 .x10 (0 : BitVec 12),
    .SD .x11 .x6 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-20 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1Copy96Function : String :=
  "blsg_copy96:\n" ++ emitProgram blsgCopy96_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgCopy96_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1Copy96Function_eq_prog :
    bls12G1Copy96Function = "blsg_copy96:\n" ++ emitProgram blsgCopy96_prog := rfl

#guard bls12G1Copy96Function.startsWith "blsg_copy96:\n"
#guard blsgCopy96_prog.length = 8
/-- Zero 96 bytes at a0 (quad loop; 8-aligned call sites only). -/
def blsgZero96_prog : Program :=
  [ .LI .x5 (12 : Word),
    .SD .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-12 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12G1Zero96Function : String :=
  "blsg_zero96:\n" ++ emitProgram blsgZero96_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgZero96_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1Zero96Function_eq_prog :
    bls12G1Zero96Function = "blsg_zero96:\n" ++ emitProgram blsgZero96_prog := rfl

#guard bls12G1Zero96Function.startsWith "blsg_zero96:\n"
#guard blsgZero96_prog.length = 6
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

/-- Double an LE affine point: a0 = input, a1 = output (96 B LE limbs,
    8-aligned, may alias). Returns a0 = 1 when the result is infinity
    (y = 0 input, which covers the all-zero infinity; output zeroed). -/
def bls12G1LeDblFunction : String :=
  "blsg_le_dbl:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  addi a0, s0, 48\n" ++
  "  li a1, 48\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_ldbl_finite\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li a0, 1\n" ++
  "  j .Lblsg_ldbl_ret\n" ++
  ".Lblsg_ldbl_finite:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_p1\n" ++
  "  .4byte 0x80d52073              # csrs 0x80D, a0 -> Bls12_381CurveDbl\n" ++
  "  la a0, blsf_p1\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  li a0, 0\n" ++
  ".Lblsg_ldbl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two LE affine points: a0 = P, a1 = Q, a2 = out (96 B LE,
    8-aligned; out may alias — checks read the originals and the result
    is copied last). Software-handles infinity, equal-x doubling, and
    P + (-P). Returns a0 = 1 when the result is infinity. -/
def bls12G1LeAddFunction : String :=
  "blsg_le_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s0\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_ladd_p_finite\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96            # P = inf: result = Q\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  j .Lblsg_ladd_ret\n" ++
  ".Lblsg_ladd_p_finite:\n" ++
  "  mv a0, s1\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  beqz a0, .Lblsg_ladd_q_finite\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_copy96            # Q = inf: result = P (finite)\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_ladd_ret\n" ++
  ".Lblsg_ladd_q_finite:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, blsg_eq48              # byte equality works on LE too\n" ++
  "  beqz a0, .Lblsg_ladd_distinct\n" ++
  "  addi a0, s0, 48\n" ++
  "  addi a1, s1, 48\n" ++
  "  jal ra, blsg_eq48\n" ++
  "  beqz a0, .Lblsg_ladd_inf       # x equal, y opposite: inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_le_dbl            # x and y equal: P + P\n" ++
  "  j .Lblsg_ladd_ret\n" ++
  ".Lblsg_ladd_distinct:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  mv a0, s1\n" ++
  "  la a1, blsf_p2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_curve_params\n" ++
  "  .4byte 0x80c52073              # csrs 0x80C, a0 -> Bls12_381CurveAdd\n" ++
  "  la a0, blsf_p1\n" ++
  "  mv a1, s2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_ladd_ret\n" ++
  ".Lblsg_ladd_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li a0, 1\n" ++
  ".Lblsg_ladd_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Multiply an affine point by a big-endian scalar (MSB-first
    double-and-add over the raw bytes, matching py_ecc `multiply`).
    a0 = scalar bytes, a1 = scalar byte length, a2 = base x||y,
    a3 = output x||y (all compact BE). The loop runs entirely on
    LE-limb points (`blsg_le_base`/`blsg_le_acc`) so the BE<->LE
    conversions happen once per scalar mul, not once per point op
    (~25x fewer steps; the 128-pair max_discount MSM rows hinge on
    this). Returns a0 = 1 when the result is infinity (output zeroed). -/
def bls12G1ScalarMulFunction : String :=
  "blsg_scalar_mul:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                      # scalar bytes\n" ++
  "  mv s7, a1                      # scalar byte length\n" ++
  "  mv s1, a2                      # base point (BE)\n" ++
  "  mv s2, a3                      # output (BE)\n" ++
  -- one-time BE -> LE conversion of the base (zeros stay zeros)
  "  mv a0, s1\n" ++
  "  la a1, blsg_le_base\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  addi a0, s1, 48\n" ++
  "  la a1, blsg_le_base\n" ++
  "  addi a1, a1, 48\n" ++
  "  jal ra, blsg_be_to_le\n" ++
  "  la a0, blsg_le_acc\n" ++
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
  "  la a0, blsg_le_acc\n" ++
  "  la a1, blsg_le_acc\n" ++
  "  jal ra, blsg_le_dbl            # alias-safe in-place double\n" ++
  "  mv s3, a0\n" ++
  ".Lblsg_mul_skip_double:\n" ++
  "  and t0, s5, s6\n" ++
  "  beqz t0, .Lblsg_mul_advance_bit\n" ++
  "  beqz s3, .Lblsg_mul_add_base\n" ++
  "  la a0, blsg_le_base\n" ++
  "  la a1, blsg_le_acc\n" ++
  "  jal ra, blsg_copy96\n" ++
  "  la a0, blsg_le_acc\n" ++
  "  li a1, 96\n" ++
  "  jal ra, blsg_is_zero_n\n" ++
  "  mv s3, a0                      # base may itself be (0,0)\n" ++
  "  j .Lblsg_mul_advance_bit\n" ++
  ".Lblsg_mul_add_base:\n" ++
  "  la a0, blsg_le_acc\n" ++
  "  la a1, blsg_le_base\n" ++
  "  la a2, blsg_le_acc\n" ++
  "  jal ra, blsg_le_add            # alias-safe in-place add\n" ++
  "  mv s3, a0\n" ++
  ".Lblsg_mul_advance_bit:\n" ++
  "  srli s6, s6, 1\n" ++
  "  j .Lblsg_mul_bit_loop\n" ++
  ".Lblsg_mul_next_byte:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lblsg_mul_byte_loop\n" ++
  ".Lblsg_mul_done:\n" ++
  "  bnez s3, .Lblsg_mul_inf_out\n" ++
  "  la a0, blsg_le_acc\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  la a0, blsg_le_acc\n" ++
  "  addi a0, a0, 48\n" ++
  "  addi a1, s2, 48\n" ++
  "  jal ra, blsg_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  j .Lblsg_mul_ret\n" ++
  ".Lblsg_mul_inf_out:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, blsg_zero96\n" ++
  "  li a0, 1\n" ++
  ".Lblsg_mul_ret:\n" ++
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
  bls12CopyQuadsFunction ++ "\n" ++
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
  bls12G1LeDblFunction ++ "\n" ++
  bls12G1LeAddFunction ++ "\n" ++
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
