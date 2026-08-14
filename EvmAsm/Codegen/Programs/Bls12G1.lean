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
import EvmAsm.Codegen.Programs.Bls12G1Eq48SAsm
import EvmAsm.Codegen.Programs.Bls12Field
import EvmAsm.Codegen.Programs.Bls12G1IsZeroNSAsm

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
/-- a0 = 1 iff the a1 bytes at a0 are all zero. Leaf.
    Re-emitted drop-in: verified single-exit SAsm body, same 12-instruction
    length as the original two-exit byte scan. -/
def blsgIsZeroN_prog : Program :=
  [ .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x6 .x0 (24 : BitVec 13),
    .LBU .x7 .x5 (0 : BitVec 12),
    .BNE .x7 .x0 (16 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x10 (1 : Word),
    .BEQ .x6 .x0 (8 : BitVec 13),
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

/-- The local generated Program block is the verified SAsm drop-in. -/
theorem blsgIsZeroN_prog_eq_verified :
    blsgIsZeroN_prog = Bls12G1IsZeroNSAsm.blsgIsZeroN_prog := rfl

/-- a0 = 1 iff the two 48-byte buffers at a0 / a1 are equal. Leaf helper.

    Re-emitted drop-in: the verified `Bls12G1Eq48SAsm.blsgEq48Body`
    flatten + `ret` (15 instructions, same length as the pre-drop-in two-exit compare). -/
def blsgEq48_prog : Program :=
  Bls12G1Eq48SAsm.blsgEq48_prog

def bls12G1Eq48Function : String :=
  "blsg_eq48:\n" ++ emitProgram blsgEq48_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsgEq48_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12G1Eq48Function_eq_prog :
    bls12G1Eq48Function = "blsg_eq48:\n" ++ emitProgram blsgEq48_prog := rfl

#guard bls12G1Eq48Function.startsWith "blsg_eq48:\n"
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

/-- Reloc side-table for `blsgLtP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgLtP_relocs : RelocTable :=
  [ (0, .la .x5 "blsg_p_be") ]

def bls12G1LtPFunction : String :=
  "blsg_lt_p:\n" ++ emitProgramR blsgLtP_prog blsgLtP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgLtP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1LtPFunction_eq_prog :
    bls12G1LtPFunction = "blsg_lt_p:\n" ++ emitProgramR blsgLtP_prog blsgLtP_relocs := rfl

#guard bls12G1LtPFunction.startsWith "blsg_lt_p:\n"
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
/-- Fp d = (a*b) mod p: a0/a1 = 48-byte BE inputs, a2 = 48-byte BE
    output, via the Arith384Mod `blsf_mul_params` block. -/
def blsgMulModP_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_a (GuestAddrs.blsg_mul_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_a (GuestAddrs.blsg_mul_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_mul_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_b (GuestAddrs.blsg_mul_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_b (GuestAddrs.blsg_mul_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_mul_mod_p + 48)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_mul_params (GuestAddrs.blsg_mul_mod_p + 52)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_mul_params (GuestAddrs.blsg_mul_mod_p + 52)),
    .CSRS (2059 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_d (GuestAddrs.blsg_mul_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_d (GuestAddrs.blsg_mul_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_mul_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgMulModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgMulModP_relocs : RelocTable :=
  [ (6, .la .x11 "blsf_le_a"),
    (8, .jal .x1 "blsg_be_to_le"),
    (10, .la .x11 "blsf_le_b"),
    (12, .jal .x1 "blsg_be_to_le"),
    (13, .la .x10 "blsf_mul_params"),
    (16, .la .x10 "blsf_le_d"),
    (19, .jal .x1 "blsg_le_to_be") ]

def bls12G1MulModPFunction : String :=
  "blsg_mul_mod_p:\n" ++ emitProgramR blsgMulModP_prog blsgMulModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgMulModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1MulModPFunction_eq_prog :
    bls12G1MulModPFunction = "blsg_mul_mod_p:\n" ++ emitProgramR blsgMulModP_prog blsgMulModP_relocs := rfl

#guard bls12G1MulModPFunction.startsWith "blsg_mul_mod_p:\n"
/-- Fp d = (a + b) mod p: same surface via `blsf_add_params`
    (`d = a*1 + b`). -/
def blsgAddModP_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_a (GuestAddrs.blsg_add_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_a (GuestAddrs.blsg_add_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_add_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_b (GuestAddrs.blsg_add_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_b (GuestAddrs.blsg_add_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_add_mod_p + 48)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_add_params (GuestAddrs.blsg_add_mod_p + 52)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_add_params (GuestAddrs.blsg_add_mod_p + 52)),
    .CSRS (2059 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_d (GuestAddrs.blsg_add_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_d (GuestAddrs.blsg_add_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_add_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgAddModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgAddModP_relocs : RelocTable :=
  [ (6, .la .x11 "blsf_le_a"),
    (8, .jal .x1 "blsg_be_to_le"),
    (10, .la .x11 "blsf_le_b"),
    (12, .jal .x1 "blsg_be_to_le"),
    (13, .la .x10 "blsf_add_params"),
    (16, .la .x10 "blsf_le_d"),
    (19, .jal .x1 "blsg_le_to_be") ]

def bls12G1AddModPFunction : String :=
  "blsg_add_mod_p:\n" ++ emitProgramR blsgAddModP_prog blsgAddModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgAddModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1AddModPFunction_eq_prog :
    bls12G1AddModPFunction = "blsg_add_mod_p:\n" ++ emitProgramR blsgAddModP_prog blsgAddModP_relocs := rfl

#guard bls12G1AddModPFunction.startsWith "blsg_add_mod_p:\n"
/-- Double an affine point. a0 = input x||y (compact BE 96), a1 = output.
    Returns a0 = 1 when the result is infinity (y = 0 input, which also
    covers the (0,0) infinity encoding), output zeroed; else 0. -/
def blsgPointDbl_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (48 : BitVec 12),
    .LI .x11 (48 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_point_dbl + 32)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_point_dbl + 44)),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.blsg_point_dbl + 144) (GuestAddrs.blsg_point_dbl + 52)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 60)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 60)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_dbl + 68)),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 76)),
    .ADDI .x11 .x11 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_dbl + 88)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 92)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 92)),
    .CSRS (2061 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 104)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_point_dbl + 116)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 120)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_dbl + 120)),
    .ADDI .x10 .x10 (48 : BitVec 12),
    .ADDI .x11 .x9 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_point_dbl + 136)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgPointDbl_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgPointDbl_relocs : RelocTable :=
  [ (8, .jal .x1 "blsg_is_zero_n"),
    (11, .jal .x1 "blsg_zero96"),
    (15, .la .x11 "blsf_p1"),
    (17, .jal .x1 "blsg_be_to_le"),
    (19, .la .x11 "blsf_p1"),
    (22, .jal .x1 "blsg_be_to_le"),
    (23, .la .x10 "blsf_p1"),
    (26, .la .x10 "blsf_p1"),
    (29, .jal .x1 "blsg_le_to_be"),
    (30, .la .x10 "blsf_p1"),
    (34, .jal .x1 "blsg_le_to_be") ]

def bls12G1PointDblFunction : String :=
  "blsg_point_dbl:\n" ++ emitProgramR blsgPointDbl_prog blsgPointDbl_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgPointDbl_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1PointDblFunction_eq_prog :
    bls12G1PointDblFunction = "blsg_point_dbl:\n" ++ emitProgramR blsgPointDbl_prog blsgPointDbl_relocs := rfl

#guard bls12G1PointDblFunction.startsWith "blsg_point_dbl:\n"
/-- Add two affine points. a0 = P, a1 = Q, a2 = out (all compact BE 96,
    infinity = all-zero). Software-handles the accelerator-excluded
    cases: P or Q at infinity, equal x with equal y (doubling), equal x
    with opposite y (infinity). Returns a0 = 1 when the result is
    infinity (output zeroed), else 0. -/
def blsgPointAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_point_add + 40)),
    .BEQ .x10 .x0 (32 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_copy96 (GuestAddrs.blsg_point_add + 56)),
    .MV .x10 .x18,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_point_add + 68)),
    .JAL .x0 (jalOff (GuestAddrs.blsg_point_add + 300) (GuestAddrs.blsg_point_add + 72)),
    .MV .x10 .x9,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_point_add + 84)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_copy96 (GuestAddrs.blsg_point_add + 100)),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.blsg_point_add + 300) (GuestAddrs.blsg_point_add + 108)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_eq48 (GuestAddrs.blsg_point_add + 120)),
    .BEQ .x10 .x0 (36 : BitVec 13),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .ADDI .x11 .x9 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_eq48 (GuestAddrs.blsg_point_add + 136)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg_point_add + 288) (GuestAddrs.blsg_point_add + 140)),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_point_dbl (GuestAddrs.blsg_point_add + 152)),
    .JAL .x0 (jalOff (GuestAddrs.blsg_point_add + 300) (GuestAddrs.blsg_point_add + 156)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 164)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 164)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_add + 172)),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 180)),
    .ADDI .x11 .x11 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_add + 192)),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p2 (GuestAddrs.blsg_point_add + 200)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p2 (GuestAddrs.blsg_point_add + 200)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_add + 208)),
    .ADDI .x10 .x9 (48 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_p2 (GuestAddrs.blsg_point_add + 216)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p2 (GuestAddrs.blsg_point_add + 216)),
    .ADDI .x11 .x11 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_point_add + 228)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_curve_params (GuestAddrs.blsg_point_add + 232)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_curve_params (GuestAddrs.blsg_point_add + 232)),
    .CSRS (2060 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 244)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 244)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_point_add + 256)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 260)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_point_add + 260)),
    .ADDI .x10 .x10 (48 : BitVec 12),
    .ADDI .x11 .x18 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_point_add + 276)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_point_add + 292)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgPointAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgPointAdd_relocs : RelocTable :=
  [ (10, .jal .x1 "blsg_is_zero_n"),
    (14, .jal .x1 "blsg_copy96"),
    (17, .jal .x1 "blsg_is_zero_n"),
    (21, .jal .x1 "blsg_is_zero_n"),
    (25, .jal .x1 "blsg_copy96"),
    (30, .jal .x1 "blsg_eq48"),
    (34, .jal .x1 "blsg_eq48"),
    (38, .jal .x1 "blsg_point_dbl"),
    (41, .la .x11 "blsf_p1"),
    (43, .jal .x1 "blsg_be_to_le"),
    (45, .la .x11 "blsf_p1"),
    (48, .jal .x1 "blsg_be_to_le"),
    (50, .la .x11 "blsf_p2"),
    (52, .jal .x1 "blsg_be_to_le"),
    (54, .la .x11 "blsf_p2"),
    (57, .jal .x1 "blsg_be_to_le"),
    (58, .la .x10 "blsf_curve_params"),
    (61, .la .x10 "blsf_p1"),
    (64, .jal .x1 "blsg_le_to_be"),
    (65, .la .x10 "blsf_p1"),
    (69, .jal .x1 "blsg_le_to_be"),
    (73, .jal .x1 "blsg_zero96") ]

def bls12G1PointAddFunction : String :=
  "blsg_point_add:\n" ++ emitProgramR blsgPointAdd_prog blsgPointAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgPointAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1PointAddFunction_eq_prog :
    bls12G1PointAddFunction = "blsg_point_add:\n" ++ emitProgramR blsgPointAdd_prog blsgPointAdd_relocs := rfl

#guard bls12G1PointAddFunction.startsWith "blsg_point_add:\n"
/-- a0 = 1 iff the finite point at a0 (coords already `< p`) satisfies
    y^2 = x^3 + 4 mod p. -/
def blsgOnCurve_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 20)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 20)),
    .JAL .x1 (jalOff GuestAddrs.blsg_mul_mod_p (GuestAddrs.blsg_on_curve + 28)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 32)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 32)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 44)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 44)),
    .JAL .x1 (jalOff GuestAddrs.blsg_mul_mod_p (GuestAddrs.blsg_on_curve + 52)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 56)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_t (GuestAddrs.blsg_on_curve + 56)),
    .AUIPC .x11 (laHi GuestAddrs.blsg_b_be (GuestAddrs.blsg_on_curve + 64)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_b_be (GuestAddrs.blsg_on_curve + 64)),
    .AUIPC .x12 (laHi GuestAddrs.blsg_rhs (GuestAddrs.blsg_on_curve + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg_rhs (GuestAddrs.blsg_on_curve + 72)),
    .JAL .x1 (jalOff GuestAddrs.blsg_add_mod_p (GuestAddrs.blsg_on_curve + 80)),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .ADDI .x11 .x8 (48 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.blsg_y2 (GuestAddrs.blsg_on_curve + 92)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg_y2 (GuestAddrs.blsg_on_curve + 92)),
    .JAL .x1 (jalOff GuestAddrs.blsg_mul_mod_p (GuestAddrs.blsg_on_curve + 100)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_rhs (GuestAddrs.blsg_on_curve + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_rhs (GuestAddrs.blsg_on_curve + 104)),
    .AUIPC .x11 (laHi GuestAddrs.blsg_y2 (GuestAddrs.blsg_on_curve + 112)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_y2 (GuestAddrs.blsg_on_curve + 112)),
    .JAL .x1 (jalOff GuestAddrs.blsg_eq48 (GuestAddrs.blsg_on_curve + 120)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgOnCurve_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgOnCurve_relocs : RelocTable :=
  [ (5, .la .x12 "blsg_t"),
    (7, .jal .x1 "blsg_mul_mod_p"),
    (8, .la .x10 "blsg_t"),
    (11, .la .x12 "blsg_t"),
    (13, .jal .x1 "blsg_mul_mod_p"),
    (14, .la .x10 "blsg_t"),
    (16, .la .x11 "blsg_b_be"),
    (18, .la .x12 "blsg_rhs"),
    (20, .jal .x1 "blsg_add_mod_p"),
    (23, .la .x12 "blsg_y2"),
    (25, .jal .x1 "blsg_mul_mod_p"),
    (26, .la .x10 "blsg_rhs"),
    (28, .la .x11 "blsg_y2"),
    (30, .jal .x1 "blsg_eq48") ]

def bls12G1OnCurveFunction : String :=
  "blsg_on_curve:\n" ++ emitProgramR blsgOnCurve_prog blsgOnCurve_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgOnCurve_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1OnCurveFunction_eq_prog :
    bls12G1OnCurveFunction = "blsg_on_curve:\n" ++ emitProgramR blsgOnCurve_prog blsgOnCurve_relocs := rfl

#guard bls12G1OnCurveFunction.startsWith "blsg_on_curve:\n"
/-- Decode one EIP-2537 G1 wire point (a0 = 128-byte padded BE record)
    into a compact 96-byte point at a1: each 64-byte field element must
    have its 16 pad bytes zero and 48-byte value < p, and the point must
    be (0,0) (infinity) or on the curve. Returns a0 = 0 (valid finite),
    1 ((0,0) infinity), or 2 (invalid encoding / off-curve). -/
def blsgDecodeG1_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .LI .x11 (16 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_decode_g1 + 32)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg_decode_g1 + 196) (GuestAddrs.blsg_decode_g1 + 36)),
    .ADDI .x10 .x8 (64 : BitVec 12),
    .LI .x11 (16 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_decode_g1 + 48)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg_decode_g1 + 196) (GuestAddrs.blsg_decode_g1 + 52)),
    .ADDI .x6 .x8 (16 : BitVec 12),
    .MV .x7 .x9,
    .LI .x5 (48 : Word),
    .LBU .x28 .x6 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-20 : BitVec 13),
    .ADDI .x6 .x8 (80 : BitVec 12),
    .ADDI .x7 .x9 (48 : BitVec 12),
    .LI .x5 (48 : Word),
    .LBU .x28 .x6 (0 : BitVec 12),
    .SB .x7 .x28 (0 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_lt_p (GuestAddrs.blsg_decode_g1 + 132)),
    .BEQ .x10 .x0 (60 : BitVec 13),
    .ADDI .x10 .x9 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_lt_p (GuestAddrs.blsg_decode_g1 + 144)),
    .BEQ .x10 .x0 (48 : BitVec 13),
    .MV .x10 .x9,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_decode_g1 + 160)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (28 : BitVec 21),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_on_curve (GuestAddrs.blsg_decode_g1 + 180)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgDecodeG1_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgDecodeG1_relocs : RelocTable :=
  [ (8, .jal .x1 "blsg_is_zero_n"),
    (12, .jal .x1 "blsg_is_zero_n"),
    (33, .jal .x1 "blsg_lt_p"),
    (36, .jal .x1 "blsg_lt_p"),
    (40, .jal .x1 "blsg_is_zero_n"),
    (45, .jal .x1 "blsg_on_curve") ]

def bls12G1DecodeFunction : String :=
  "blsg_decode_g1:\n" ++ emitProgramR blsgDecodeG1_prog blsgDecodeG1_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgDecodeG1_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1DecodeFunction_eq_prog :
    bls12G1DecodeFunction = "blsg_decode_g1:\n" ++ emitProgramR blsgDecodeG1_prog blsgDecodeG1_relocs := rfl

#guard bls12G1DecodeFunction.startsWith "blsg_decode_g1:\n"
/-- Double an LE affine point: a0 = input, a1 = output (96 B LE limbs,
    8-aligned, may alias). Returns a0 = 1 when the result is infinity
    (y = 0 input, which covers the all-zero infinity; output zeroed). -/
def blsgLeDbl_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (48 : BitVec 12),
    .LI .x11 (48 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_le_dbl + 32)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_le_dbl + 44)),
    .LI .x10 (1 : Word),
    .JAL .x0 (60 : BitVec 21),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 60)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 60)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg_le_dbl + 72)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 76)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 76)),
    .CSRS (2061 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 88)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_dbl + 88)),
    .MV .x11 .x9,
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg_le_dbl + 104)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgLeDbl_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgLeDbl_relocs : RelocTable :=
  [ (8, .jal .x1 "blsg_is_zero_n"),
    (11, .jal .x1 "blsg_zero96"),
    (15, .la .x11 "blsf_p1"),
    (18, .jal .x1 "blsf_copy_quads"),
    (19, .la .x10 "blsf_p1"),
    (22, .la .x10 "blsf_p1"),
    (26, .jal .x1 "blsf_copy_quads") ]

def bls12G1LeDblFunction : String :=
  "blsg_le_dbl:\n" ++ emitProgramR blsgLeDbl_prog blsgLeDbl_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgLeDbl_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1LeDblFunction_eq_prog :
    bls12G1LeDblFunction = "blsg_le_dbl:\n" ++ emitProgramR blsgLeDbl_prog blsgLeDbl_relocs := rfl

#guard bls12G1LeDblFunction.startsWith "blsg_le_dbl:\n"
/-- Add two LE affine points: a0 = P, a1 = Q, a2 = out (96 B LE,
    8-aligned; out may alias — checks read the originals and the result
    is copied last). Software-handles infinity, equal-x doubling, and
    P + (-P). Returns a0 = 1 when the result is infinity. -/
def blsgLeAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_le_add + 40)),
    .BEQ .x10 .x0 (32 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_copy96 (GuestAddrs.blsg_le_add + 56)),
    .MV .x10 .x18,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_le_add + 68)),
    .JAL .x0 (jalOff (GuestAddrs.blsg_le_add + 252) (GuestAddrs.blsg_le_add + 72)),
    .MV .x10 .x9,
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_le_add + 84)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_copy96 (GuestAddrs.blsg_le_add + 100)),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.blsg_le_add + 252) (GuestAddrs.blsg_le_add + 108)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg_eq48 (GuestAddrs.blsg_le_add + 120)),
    .BEQ .x10 .x0 (36 : BitVec 13),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .ADDI .x11 .x9 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_eq48 (GuestAddrs.blsg_le_add + 136)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg_le_add + 240) (GuestAddrs.blsg_le_add + 140)),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_dbl (GuestAddrs.blsg_le_add + 152)),
    .JAL .x0 (jalOff (GuestAddrs.blsg_le_add + 252) (GuestAddrs.blsg_le_add + 156)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_add + 164)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_add + 164)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg_le_add + 176)),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.blsf_p2 (GuestAddrs.blsg_le_add + 184)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_p2 (GuestAddrs.blsg_le_add + 184)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg_le_add + 196)),
    .AUIPC .x10 (laHi GuestAddrs.blsf_curve_params (GuestAddrs.blsg_le_add + 200)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_curve_params (GuestAddrs.blsg_le_add + 200)),
    .CSRS (2060 : BitVec 12) .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_add + 212)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_p1 (GuestAddrs.blsg_le_add + 212)),
    .MV .x11 .x18,
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg_le_add + 228)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_le_add + 244)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgLeAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgLeAdd_relocs : RelocTable :=
  [ (10, .jal .x1 "blsg_is_zero_n"),
    (14, .jal .x1 "blsg_copy96"),
    (17, .jal .x1 "blsg_is_zero_n"),
    (21, .jal .x1 "blsg_is_zero_n"),
    (25, .jal .x1 "blsg_copy96"),
    (30, .jal .x1 "blsg_eq48"),
    (34, .jal .x1 "blsg_eq48"),
    (38, .jal .x1 "blsg_le_dbl"),
    (41, .la .x11 "blsf_p1"),
    (44, .jal .x1 "blsf_copy_quads"),
    (46, .la .x11 "blsf_p2"),
    (49, .jal .x1 "blsf_copy_quads"),
    (50, .la .x10 "blsf_curve_params"),
    (53, .la .x10 "blsf_p1"),
    (57, .jal .x1 "blsf_copy_quads"),
    (61, .jal .x1 "blsg_zero96") ]

def bls12G1LeAddFunction : String :=
  "blsg_le_add:\n" ++ emitProgramR blsgLeAdd_prog blsgLeAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgLeAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1LeAddFunction_eq_prog :
    bls12G1LeAddFunction = "blsg_le_add:\n" ++ emitProgramR blsgLeAdd_prog blsgLeAdd_relocs := rfl

#guard bls12G1LeAddFunction.startsWith "blsg_le_add:\n"
/-- Multiply an affine point by a big-endian scalar (MSB-first
    double-and-add over the raw bytes, matching py_ecc `multiply`).
    a0 = scalar bytes, a1 = scalar byte length, a2 = base x||y,
    a3 = output x||y (all compact BE). The loop runs entirely on
    LE-limb points (`blsg_le_base`/`blsg_le_acc`) so the BE<->LE
    conversions happen once per scalar mul, not once per point op
    (~25x fewer steps; the 128-pair max_discount MSM rows hinge on
    this). Returns a0 = 1 when the result is infinity (output zeroed). -/
def blsgScalarMul_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .SD .x2 .x23 (64 : BitVec 12),
    .MV .x8 .x10,
    .MV .x23 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 60)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 60)),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_scalar_mul + 68)),
    .ADDI .x10 .x9 (48 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 76)),
    .ADDI .x11 .x11 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg_scalar_mul + 88)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 92)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 92)),
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_scalar_mul + 100)),
    .LI .x19 (1 : Word),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x23 (brOff (GuestAddrs.blsg_scalar_mul + 264) (GuestAddrs.blsg_scalar_mul + 112)),
    .ADD .x5 .x8 .x20,
    .LBU .x21 .x5 (0 : BitVec 12),
    .LI .x22 (128 : Word),
    .BEQ .x22 .x0 (brOff (GuestAddrs.blsg_scalar_mul + 256) (GuestAddrs.blsg_scalar_mul + 128)),
    .BNE .x19 .x0 (28 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 136)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 136)),
    .AUIPC .x11 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 144)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 144)),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_dbl (GuestAddrs.blsg_scalar_mul + 152)),
    .MV .x19 .x10,
    .AND .x5 .x21 .x22,
    .BEQ .x5 .x0 (brOff (GuestAddrs.blsg_scalar_mul + 248) (GuestAddrs.blsg_scalar_mul + 164)),
    .BEQ .x19 .x0 (48 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 172)),
    .AUIPC .x11 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 180)),
    .JAL .x1 (jalOff GuestAddrs.blsg_copy96 (GuestAddrs.blsg_scalar_mul + 188)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 192)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 192)),
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg_scalar_mul + 204)),
    .MV .x19 .x10,
    .JAL .x0 (36 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 216)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 216)),
    .AUIPC .x11 (laHi GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 224)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg_le_base (GuestAddrs.blsg_scalar_mul + 224)),
    .AUIPC .x12 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 232)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 232)),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_add (GuestAddrs.blsg_scalar_mul + 240)),
    .MV .x19 .x10,
    .SRLI .x22 .x22 (1 : BitVec 6),
    .JAL .x0 (jalOff (GuestAddrs.blsg_scalar_mul + 128) (GuestAddrs.blsg_scalar_mul + 252)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.blsg_scalar_mul + 112) (GuestAddrs.blsg_scalar_mul + 260)),
    .BNE .x19 .x0 (48 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 268)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 268)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_scalar_mul + 280)),
    .AUIPC .x10 (laHi GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 284)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_le_acc (GuestAddrs.blsg_scalar_mul + 284)),
    .ADDI .x10 .x10 (48 : BitVec 12),
    .ADDI .x11 .x18 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg_scalar_mul + 300)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg_zero96 (GuestAddrs.blsg_scalar_mul + 316)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgScalarMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgScalarMul_relocs : RelocTable :=
  [ (15, .la .x11 "blsg_le_base"),
    (17, .jal .x1 "blsg_be_to_le"),
    (19, .la .x11 "blsg_le_base"),
    (22, .jal .x1 "blsg_be_to_le"),
    (23, .la .x10 "blsg_le_acc"),
    (25, .jal .x1 "blsg_zero96"),
    (34, .la .x10 "blsg_le_acc"),
    (36, .la .x11 "blsg_le_acc"),
    (38, .jal .x1 "blsg_le_dbl"),
    (43, .la .x10 "blsg_le_base"),
    (45, .la .x11 "blsg_le_acc"),
    (47, .jal .x1 "blsg_copy96"),
    (48, .la .x10 "blsg_le_acc"),
    (51, .jal .x1 "blsg_is_zero_n"),
    (54, .la .x10 "blsg_le_acc"),
    (56, .la .x11 "blsg_le_base"),
    (58, .la .x12 "blsg_le_acc"),
    (60, .jal .x1 "blsg_le_add"),
    (67, .la .x10 "blsg_le_acc"),
    (70, .jal .x1 "blsg_le_to_be"),
    (71, .la .x10 "blsg_le_acc"),
    (75, .jal .x1 "blsg_le_to_be"),
    (79, .jal .x1 "blsg_zero96") ]

def bls12G1ScalarMulFunction : String :=
  "blsg_scalar_mul:\n" ++ emitProgramR blsgScalarMul_prog blsgScalarMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgScalarMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1ScalarMulFunction_eq_prog :
    bls12G1ScalarMulFunction = "blsg_scalar_mul:\n" ++ emitProgramR blsgScalarMul_prog blsgScalarMul_relocs := rfl

#guard bls12G1ScalarMulFunction.startsWith "blsg_scalar_mul:\n"
/-- EIP-2537 G1 subgroup check: a0 = compact point. Returns a0 = 1 iff
    n*P = inf (P in the order-n subgroup; infinity passes trivially).
    The G1 cofactor is not 1, so this is a REAL check, unlike BN254. -/
def blsgSubgroupG1_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x12 .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsg_n_be (GuestAddrs.blsg_subgroup_g1 + 12)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_n_be (GuestAddrs.blsg_subgroup_g1 + 12)),
    .LI .x11 (32 : Word),
    .AUIPC .x13 (laHi GuestAddrs.blsg_sub_out (GuestAddrs.blsg_subgroup_g1 + 24)),
    .ADDI .x13 .x13 (laLo GuestAddrs.blsg_sub_out (GuestAddrs.blsg_subgroup_g1 + 24)),
    .JAL .x1 (jalOff GuestAddrs.blsg_scalar_mul (GuestAddrs.blsg_subgroup_g1 + 32)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsgSubgroupG1_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsgSubgroupG1_relocs : RelocTable :=
  [ (3, .la .x10 "blsg_n_be"),
    (6, .la .x13 "blsg_sub_out"),
    (8, .jal .x1 "blsg_scalar_mul") ]

def bls12G1SubgroupFunction : String :=
  "blsg_subgroup_g1:\n" ++ emitProgramR blsgSubgroupG1_prog blsgSubgroupG1_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsgSubgroupG1_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G1SubgroupFunction_eq_prog :
    bls12G1SubgroupFunction = "blsg_subgroup_g1:\n" ++ emitProgramR blsgSubgroupG1_prog blsgSubgroupG1_relocs := rfl

#guard bls12G1SubgroupFunction.startsWith "blsg_subgroup_g1:\n"
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


end EvmAsm.Codegen
