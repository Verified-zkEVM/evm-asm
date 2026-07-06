/-
  EvmAsm.Codegen.Programs.Secp256k1Curve

  Codegen-only affine secp256k1 curve helpers for staged software public-key
  recovery. Points are 64-byte big-endian affine records: x || y.

  `secp256k1_point_add` / `secp256k1_point_double` are backed by the ziskemu
  Secp256k1Add/Secp256k1Dbl accelerators (`csrs 0x803` / `csrs 0x804` with a
  little-endian-limb parameter pointer, emitted as pre-encoded `.4byte`s for
  the plain `rv64imac` toolchain). The affine special cases the accelerators
  exclude (input at infinity, doubling with y = 0, adding points with equal
  x) stay in software, preserving the original call surface and return codes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64

private def generatorPointAsm : String :=
  "  .byte 0x79,0xbe,0x66,0x7e,0xf9,0xdc,0xbb,0xac\n" ++
  "  .byte 0x55,0xa0,0x62,0x95,0xce,0x87,0x0b,0x07\n" ++
  "  .byte 0x02,0x9b,0xfc,0xdb,0x2d,0xce,0x28,0xd9\n" ++
  "  .byte 0x59,0xf2,0x81,0x5b,0x16,0xf8,0x17,0x98\n" ++
  "  .byte 0x48,0x3a,0xda,0x77,0x26,0xa3,0xc4,0x65\n" ++
  "  .byte 0x5d,0xa4,0xfb,0xfc,0x0e,0x11,0x08,0xa8\n" ++
  "  .byte 0xfd,0x17,0xb4,0x48,0xa6,0x85,0x54,0x19\n" ++
  "  .byte 0x9c,0x47,0xd0,0x8f,0xfb,0x10,0xd4,0xb8\n"

private def generator2PointAsm : String :=
  "  .byte 0xc6,0x04,0x7f,0x94,0x41,0xed,0x7d,0x6d\n" ++
  "  .byte 0x30,0x45,0x40,0x6e,0x95,0xc0,0x7c,0xd8\n" ++
  "  .byte 0x5c,0x77,0x8e,0x4b,0x8c,0xef,0x3c,0xa7\n" ++
  "  .byte 0xab,0xac,0x09,0xb9,0x5c,0x70,0x9e,0xe5\n" ++
  "  .byte 0x1a,0xe1,0x68,0xfe,0xa6,0x3d,0xc3,0x39\n" ++
  "  .byte 0xa3,0xc5,0x84,0x19,0x46,0x6c,0xea,0xee\n" ++
  "  .byte 0xf7,0xf6,0x32,0x65,0x32,0x66,0xd0,0xe1\n" ++
  "  .byte 0x23,0x64,0x31,0xa9,0x50,0xcf,0xe5,0x2a\n"

def secp256k1CurveDataSection : String :=
  secp256k1FieldDataSection ++
  ".balign 8\n" ++
  "secp256k1_generator:\n" ++
  generatorPointAsm ++
  ".balign 8\n" ++
  "secp256k1_generator_2:\n" ++
  generator2PointAsm ++
  ".balign 8\n" ++
  "secc_point_tmp:\n  .zero 64\n" ++
  -- Little-endian limb staging for the ziskemu Secp256k1Add/Dbl accelerators
  -- (x||y, four u64 limbs per coordinate, least-significant limb first) plus
  -- the static Secp256k1Add parameter block {&p1, &p2}; the result lands in p1.
  "secc_le_p1:\n  .zero 64\n" ++
  "secc_le_p2:\n  .zero 64\n" ++
  "secc_add_params:\n  .quad secc_le_p1, secc_le_p2\n"

/-- Double an affine point. a0=input x||y, a1=output x||y. Returns 1 for infinity. -/
def secp256k1PointDouble_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secp256k1_point_double + 28)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 40)),
    .ADDI .x10 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_point_double + 48)),
    .LI .x10 (1 : Word),
    .JAL .x0 (92 : BitVec 21),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 64)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 64)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secp256k1_point_double + 72)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 80)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 80)),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secp256k1_point_double + 92)),
    .AUIPC .x5 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 96)),
    .CSRS (2052 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 108)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 108)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secp256k1_point_double + 120)),
    .AUIPC .x10 (laHi GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 124)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_le_p1 (GuestAddrs.secp256k1_point_double + 124)),
    .ADDI .x10 .x10 (32 : BitVec 12),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secp256k1_point_double + 140)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secp256k1PointDouble_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secp256k1PointDouble_relocs : RelocTable :=
  [ (7, .jal .x1 "secf_is_zero32"),
    (10, .jal .x1 "secf_zero32"),
    (12, .jal .x1 "secf_zero32"),
    (16, .la .x11 "secc_le_p1"),
    (18, .jal .x1 "secf_be_to_le"),
    (20, .la .x11 "secc_le_p1"),
    (23, .jal .x1 "secf_be_to_le"),
    (24, .la .x5 "secc_le_p1"),
    (27, .la .x10 "secc_le_p1"),
    (30, .jal .x1 "secf_le_to_be"),
    (31, .la .x10 "secc_le_p1"),
    (35, .jal .x1 "secf_le_to_be") ]

def secp256k1PointDoubleFunction : String :=
  "secp256k1_point_double:\n" ++ emitProgramR secp256k1PointDouble_prog secp256k1PointDouble_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secp256k1PointDouble_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1PointDoubleFunction_eq_prog :
    secp256k1PointDoubleFunction = "secp256k1_point_double:\n" ++ emitProgramR secp256k1PointDouble_prog secp256k1PointDouble_relocs := rfl

#guard secp256k1PointDoubleFunction.startsWith "secp256k1_point_double:\n"
#guard secp256k1PointDouble_prog.length = 42
/-- Add two affine points. a0=P, a1=Q, a2=out. Returns 1 for infinity. -/
def secp256k1PointAddFunction : String :=
  "secp256k1_point_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  -- The scalar-mul helper represents the point at infinity as zero64. Treat it
  -- as the additive identity before using the affine accelerator.
  "  mv a0, s0\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecc_add_check_q_inf\n" ++
  "  addi a0, s0, 32\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecc_add_check_q_inf\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secp256k1_point_copy64\n" ++
  "  li a0, 0\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_check_q_inf:\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecc_add_regular\n" ++
  "  addi a0, s1, 32\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecc_add_regular\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secp256k1_point_copy64\n" ++
  "  li a0, 0\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_regular:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_eq32\n" ++
  "  beqz a0, .Lsecc_add_distinct_x\n" ++
  "  addi a0, s0, 32\n" ++
  "  addi a1, s1, 32\n" ++
  "  jal ra, secf_eq32\n" ++
  "  beqz a0, .Lsecc_add_inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secp256k1_point_double\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_distinct_x:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secc_le_p1\n" ++
  "  jal ra, secf_be_to_le         # p1.x\n" ++
  "  addi a0, s0, 32\n" ++
  "  la a1, secc_le_p1\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, secf_be_to_le         # p1.y\n" ++
  "  mv a0, s1\n" ++
  "  la a1, secc_le_p2\n" ++
  "  jal ra, secf_be_to_le         # p2.x\n" ++
  "  addi a0, s1, 32\n" ++
  "  la a1, secc_le_p2\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, secf_be_to_le         # p2.y\n" ++
  "  la t0, secc_add_params\n" ++
  "  .4byte 0x8032a073             # csrs 0x803, t0 -> Secp256k1Add\n" ++
  "  la a0, secc_le_p1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_le_to_be         # out.x\n" ++
  "  la a0, secc_le_p1\n" ++
  "  addi a0, a0, 32\n" ++
  "  addi a1, s2, 32\n" ++
  "  jal ra, secf_le_to_be         # out.y\n" ++
  "  li a0, 0\n" ++
  "  j .Lsecc_add_ret\n" ++
  ".Lsecc_add_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, secf_zero32\n" ++
  "  addi a0, s2, 32\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  ".Lsecc_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"


def secp256k1PointCopy64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12),
    .SB .x11 .x6 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def secp256k1PointCopy64Function : String :=
  "secp256k1_point_copy64:\n" ++ emitProgram secp256k1PointCopy64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secp256k1PointCopy64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1PointCopy64Function_eq_prog :
    secp256k1PointCopy64Function = "secp256k1_point_copy64:\n" ++ emitProgram secp256k1PointCopy64_prog := rfl

#guard secp256k1PointCopy64Function.startsWith "secp256k1_point_copy64:\n"
#guard secp256k1PointCopy64_prog.length = 9
def secp256k1PointZero64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .BEQ .x5 .x0 (20 : BitVec 13),
    .SB .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def secp256k1PointZero64Function : String :=
  "secp256k1_point_zero64:\n" ++ emitProgram secp256k1PointZero64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secp256k1PointZero64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1PointZero64Function_eq_prog :
    secp256k1PointZero64Function = "secp256k1_point_zero64:\n" ++ emitProgram secp256k1PointZero64_prog := rfl

#guard secp256k1PointZero64Function.startsWith "secp256k1_point_zero64:\n"
#guard secp256k1PointZero64_prog.length = 7
/-- Multiply an affine point by a 256-bit big-endian scalar.
    a0=scalar32, a1=base x||y, a2=output x||y. Returns 1 when the result is
    the point at infinity, represented as zeroed output. -/
def secp256k1ScalarMul_prog : Program :=
  [ .ADDI .x2 .x2 (-72 : BitVec 12),
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
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_zero64 (GuestAddrs.secp256k1_scalar_mul + 56)),
    .LI .x19 (1 : Word),
    .LI .x20 (0 : Word),
    .LI .x5 (32 : Word),
    .BGEU .x20 .x5 (148 : BitVec 13),
    .ADD .x5 .x8 .x20,
    .LBU .x21 .x5 (0 : BitVec 12),
    .LI .x22 (128 : Word),
    .BEQ .x22 .x0 (124 : BitVec 13),
    .BNE .x19 .x0 (40 : BitVec 13),
    .MV .x10 .x18,
    .AUIPC .x11 (laHi GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 100)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 100)),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_double (GuestAddrs.secp256k1_scalar_mul + 108)),
    .MV .x19 .x10,
    .AUIPC .x10 (laHi GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 116)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_copy64 (GuestAddrs.secp256k1_scalar_mul + 128)),
    .AND .x5 .x21 .x22,
    .BEQ .x5 .x0 (68 : BitVec 13),
    .BEQ .x19 .x0 (24 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_copy64 (GuestAddrs.secp256k1_scalar_mul + 152)),
    .LI .x19 (0 : Word),
    .JAL .x0 (44 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 172)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 172)),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_add (GuestAddrs.secp256k1_scalar_mul + 180)),
    .MV .x19 .x10,
    .AUIPC .x10 (laHi GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 188)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secc_point_tmp (GuestAddrs.secp256k1_scalar_mul + 188)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_copy64 (GuestAddrs.secp256k1_scalar_mul + 200)),
    .SRLI .x22 .x22 (1 : BitVec 6),
    .JAL .x0 (-120 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-148 : BitVec 21),
    .MV .x10 .x19,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .ADDI .x2 .x2 (72 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secp256k1ScalarMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secp256k1ScalarMul_relocs : RelocTable :=
  [ (14, .jal .x1 "secp256k1_point_zero64"),
    (25, .la .x11 "secc_point_tmp"),
    (27, .jal .x1 "secp256k1_point_double"),
    (29, .la .x10 "secc_point_tmp"),
    (32, .jal .x1 "secp256k1_point_copy64"),
    (38, .jal .x1 "secp256k1_point_copy64"),
    (43, .la .x12 "secc_point_tmp"),
    (45, .jal .x1 "secp256k1_point_add"),
    (47, .la .x10 "secc_point_tmp"),
    (50, .jal .x1 "secp256k1_point_copy64") ]

def secp256k1ScalarMulFunction : String :=
  "secp256k1_scalar_mul:\n" ++ emitProgramR secp256k1ScalarMul_prog secp256k1ScalarMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secp256k1ScalarMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarMulFunction_eq_prog :
    secp256k1ScalarMulFunction = "secp256k1_scalar_mul:\n" ++ emitProgramR secp256k1ScalarMul_prog secp256k1ScalarMul_relocs := rfl

#guard secp256k1ScalarMulFunction.startsWith "secp256k1_scalar_mul:\n"
#guard secp256k1ScalarMul_prog.length = 67
/-- Curve suite over `secp256k1FieldCommonFunctionsNoU256`, for closures that
    already link the generic u256 helpers. -/
def secp256k1CurveCommonFunctionsNoU256 : String :=
  secp256k1FieldCommonFunctionsNoU256 ++ "\n" ++
  secp256k1PointDoubleFunction ++ "\n" ++
  secp256k1PointAddFunction ++ "\n" ++
  secp256k1PointCopy64Function ++ "\n" ++
  secp256k1PointZero64Function ++ "\n" ++
  secp256k1ScalarMulFunction

def secp256k1CurveCommonFunctions : String :=
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  secp256k1FieldCommonFunctionsNoU256 ++ "\n" ++
  secp256k1PointDoubleFunction ++ "\n" ++
  secp256k1PointAddFunction ++ "\n" ++
  secp256k1PointCopy64Function ++ "\n" ++
  secp256k1PointZero64Function ++ "\n" ++
  secp256k1ScalarMulFunction

def ziskSecp256k1CurvePointOpsPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, secp256k1_generator\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secp256k1_point_double\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la a0, secp256k1_generator\n" ++
  "  la a1, secp256k1_generator\n" ++
  "  li a2, 0xa0010050\n" ++
  "  jal ra, secp256k1_point_add\n" ++
  "  li t0, 0xa0010048\n" ++
  "  sd a0, 0(t0)\n" ++
  "  li a0, 0x40000008\n" ++
  "  la a1, secp256k1_generator\n" ++
  "  li a2, 0xa0010098\n" ++
  "  jal ra, secp256k1_scalar_mul\n" ++
  "  li t0, 0xa0010090\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecc_probe_done\n" ++
  secp256k1CurveCommonFunctions ++ "\n" ++
  ".Lsecc_probe_done:"

def ziskSecp256k1CurvePointOpsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1CurvePointOpsPrologue
  dataAsm     := secp256k1CurveDataSection
}

private def secp256k1ZiskLittleLimbPointData : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "secp256k1_zisk_g_add:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  "secp256k1_zisk_g_add_rhs:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  "secp256k1_zisk_g_dbl:\n" ++
  "  .quad 0x59f2815b16f81798\n" ++
  "  .quad 0x029bfcdb2dce28d9\n" ++
  "  .quad 0x55a06295ce870b07\n" ++
  "  .quad 0x79be667ef9dcbbac\n" ++
  "  .quad 0x9c47d08ffb10d4b8\n" ++
  "  .quad 0xfd17b448a6855419\n" ++
  "  .quad 0x5da4fbfc0e1108a8\n" ++
  "  .quad 0x483ada7726a3c465\n" ++
  ".balign 8\n" ++
  "secp256k1_zisk_add_args:\n" ++
  "  .quad secp256k1_zisk_g_add\n" ++
  "  .quad secp256k1_zisk_g_add_rhs\n"

private def secp256k1ZiskAddDblProbePrologue
    (addSymbol dblSymbol : String) : String :=
  "  li sp, 0xa0050000\n" ++
  "  la a0, secp256k1_zisk_add_args\n" ++
  "  jal ra, " ++ addSymbol ++ "\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, secp256k1_zisk_g_add\n" ++
  "  li t2, 8\n" ++
  "  addi t0, t0, 8\n" ++
  ".Lsecp256k1_zisk_copy_add:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lsecp256k1_zisk_copy_add\n" ++
  "  la a0, secp256k1_zisk_g_dbl\n" ++
  "  jal ra, " ++ dblSymbol ++ "\n" ++
  "  sd a0, 0(t0)\n" ++
  "  la t1, secp256k1_zisk_g_dbl\n" ++
  "  li t2, 8\n" ++
  "  addi t0, t0, 8\n" ++
  ".Lsecp256k1_zisk_copy_dbl:\n" ++
  "  ld t3, 0(t1)\n" ++
  "  sd t3, 0(t0)\n" ++
  "  addi t1, t1, 8\n" ++
  "  addi t0, t0, 8\n" ++
  "  addi t2, t2, -1\n" ++
  "  bnez t2, .Lsecp256k1_zisk_copy_dbl\n"

def ziskSecp256k1AddDblSyscallProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := secp256k1ZiskAddDblProbePrologue
    "syscall_secp256k1_add" "syscall_secp256k1_dbl"
  dataAsm     := secp256k1ZiskLittleLimbPointData
}

def ziskSecp256k1AddDblOpcodeProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := secp256k1ZiskAddDblProbePrologue
    "_opcode_secp256k1_add" "_opcode_secp256k1_dbl"
  dataAsm     := secp256k1ZiskLittleLimbPointData
}

end EvmAsm.Codegen
