/-
  EvmAsm.Codegen.Programs.Bn254Fp2

  BN254 quadratic-extension field layer for the alt_bn128 ecPairing
  precompile (0x08), bead evm-asm-fhsxz.2.4.2.62.10.1 layer 1.

  Fp2 = Fp[u]/(u^2 + 1). Elements are 64-byte, 8-aligned buffers in the
  ziskemu accelerator's NATIVE little-endian u64-limb format
  (`SyscallComplex256`): x0 limbs LSB-first at +0, x1 limbs at +32. The
  whole pairing tower stays in this format — big-endian conversions
  happen only at the precompile input/output boundary — so every Fp2
  add/sub/mul is a single accelerator call with no staging copies:

    * Bn254ComplexAdd  csrs 0x808  (.4byte 0x8082a073)
    * Bn254ComplexSub  csrs 0x809  (.4byte 0x8092a073)
    * Bn254ComplexMul  csrs 0x80A  (.4byte 0x80a2a073)

  Each takes a {&f1, &f2} parameter block and writes the result into f1,
  so the Fp2 ops here use a mutating dst ◦= src convention. Base-field
  (Fp, 32-byte LE) mul/add reuse the Arith256Mod accelerator (csrs
  0x802) with parameter blocks pointing directly at LE buffers, and the
  Fp inverse is Fermat (x^(p-2), 254-bit square-and-multiply). Inputs
  must be reduced (< p); every accelerator output is fully reduced.

  All labels are `bnp_`-prefixed; constants `bnf_le_p` / `bnf_le_zero` /
  `bnf_le_one` come from `Bn254Field.lean`'s data fragment.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bn254Field

namespace EvmAsm.Codegen

/-- Probe-only PC placeholder; unlinked from guest. bnp_fp2_inv -/
def bnpFp2InvPc : Nat := 0x80000000

/-- Probe-only data placeholders (unlinked inv consumer; not in GuestAddrs). -/
def bnpT0Placeholder : Nat := 0xa0b00000
def bnpT1Placeholder : Nat := 0xa0b00000
def bnpT2Placeholder : Nat := 0xa0b00000
def bnpPMinus1LePlaceholder : Nat := 0xa0b00000
def bnpPMinus2LePlaceholder : Nat := 0xa0b00000

open EvmAsm.Rv64

/-- Pairing-layer data labels WITHOUT a `.section .data` header (see
    `bn254FieldDataFragment`). Parameter-block scratch + the Fermat /
    negation constants. -/
def bn254Fp2DataFragment : String :=
  ".balign 8\n" ++
  -- {f1, f2} block for the three complex accelerators (result -> f1).
  "bnp_cplx_params:\n  .zero 16\n" ++
  -- {a, b, c, module, d} block for Arith256Mod-backed Fp ops.
  "bnp_arith_params:\n  .zero 40\n" ++
  -- p - 2 (the Fermat inverse exponent) and p - 1 (the negation
  -- multiplier) as LE u64 limbs.
  "bnp_p_minus_2_le:\n" ++
  "  .quad 0x3C208C16D87CFD45, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnp_p_minus_1_le:\n" ++
  "  .quad 0x3C208C16D87CFD46, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  -- Fp scratch cells (32 B LE) + one Fp2 scratch (64 B LE).
  "bnp_t0:\n  .zero 32\n" ++
  "bnp_t1:\n  .zero 32\n" ++
  "bnp_t2:\n  .zero 32\n" ++
  "bnp_fp2_t:\n  .zero 64\n"

/-- Standalone `.data` section (field constants + pairing scratch) for
    focused probes. -/
def bn254Fp2DataSection : String :=
  bn254FieldDataSection ++ bn254Fp2DataFragment

/-- Fp2 dst += src (LE 64-byte buffers). Leaf; clobbers t0. -/
def bnpFp2Add_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_add + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_add + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .CSRS (2056 : BitVec 12) .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFp2Add_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFp2Add_relocs : RelocTable :=
  [ (0, .la .x5 "bnp_cplx_params") ]

def bn254Fp2AddFunction : String :=
  "bnp_fp2_add:\n" ++ emitProgramR bnpFp2Add_prog bnpFp2Add_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFp2Add_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fp2AddFunction_eq_prog :
    bn254Fp2AddFunction = "bnp_fp2_add:\n" ++ emitProgramR bnpFp2Add_prog bnpFp2Add_relocs := rfl

#guard bn254Fp2AddFunction.startsWith "bnp_fp2_add:\n"
#guard bnpFp2Add_prog.length = 6
/-- Fp2 dst -= src. Leaf; clobbers t0. -/
def bnpFp2Sub_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_sub + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_sub + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .CSRS (2057 : BitVec 12) .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFp2Sub_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFp2Sub_relocs : RelocTable :=
  [ (0, .la .x5 "bnp_cplx_params") ]

def bn254Fp2SubFunction : String :=
  "bnp_fp2_sub:\n" ++ emitProgramR bnpFp2Sub_prog bnpFp2Sub_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFp2Sub_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fp2SubFunction_eq_prog :
    bn254Fp2SubFunction = "bnp_fp2_sub:\n" ++ emitProgramR bnpFp2Sub_prog bnpFp2Sub_relocs := rfl

#guard bn254Fp2SubFunction.startsWith "bnp_fp2_sub:\n"
#guard bnpFp2Sub_prog.length = 6
/-- Fp2 dst *= src ((x0 + x1 u)(y0 + y1 u), u^2 = -1). Leaf; clobbers t0. -/
def bnpFp2Mul_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_mul + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_cplx_params (GuestAddrs.bnp_fp2_mul + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .CSRS (2058 : BitVec 12) .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFp2Mul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFp2Mul_relocs : RelocTable :=
  [ (0, .la .x5 "bnp_cplx_params") ]

def bn254Fp2MulFunction : String :=
  "bnp_fp2_mul:\n" ++ emitProgramR bnpFp2Mul_prog bnpFp2Mul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFp2Mul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fp2MulFunction_eq_prog :
    bn254Fp2MulFunction = "bnp_fp2_mul:\n" ++ emitProgramR bnpFp2Mul_prog bnpFp2Mul_relocs := rfl

#guard bn254Fp2MulFunction.startsWith "bnp_fp2_mul:\n"
#guard bnpFp2Mul_prog.length = 6
/-- Copy a 64-byte LE Fp2 value: a0 = src, a1 = dst (both 8-aligned). -/
def bnpFp2Copy_prog : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .LD .x5 .x10 (8 : BitVec 12),
    .SD .x11 .x5 (8 : BitVec 12),
    .LD .x5 .x10 (16 : BitVec 12),
    .SD .x11 .x5 (16 : BitVec 12),
    .LD .x5 .x10 (24 : BitVec 12),
    .SD .x11 .x5 (24 : BitVec 12),
    .LD .x5 .x10 (32 : BitVec 12),
    .SD .x11 .x5 (32 : BitVec 12),
    .LD .x5 .x10 (40 : BitVec 12),
    .SD .x11 .x5 (40 : BitVec 12),
    .LD .x5 .x10 (48 : BitVec 12),
    .SD .x11 .x5 (48 : BitVec 12),
    .LD .x5 .x10 (56 : BitVec 12),
    .SD .x11 .x5 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fp2CopyFunction : String :=
  "bnp_fp2_copy:\n" ++ emitProgram bnpFp2Copy_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnpFp2Copy_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fp2CopyFunction_eq_prog :
    bn254Fp2CopyFunction = "bnp_fp2_copy:\n" ++ emitProgram bnpFp2Copy_prog := rfl

#guard bn254Fp2CopyFunction.startsWith "bnp_fp2_copy:\n"
#guard bnpFp2Copy_prog.length = 17
/-- Zero a 64-byte LE Fp2 value at a0 (8-aligned). -/
def bnpFp2Zero_prog : Program :=
  [ .SD .x10 .x0 (0 : BitVec 12),
    .SD .x10 .x0 (8 : BitVec 12),
    .SD .x10 .x0 (16 : BitVec 12),
    .SD .x10 .x0 (24 : BitVec 12),
    .SD .x10 .x0 (32 : BitVec 12),
    .SD .x10 .x0 (40 : BitVec 12),
    .SD .x10 .x0 (48 : BitVec 12),
    .SD .x10 .x0 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fp2ZeroFunction : String :=
  "bnp_fp2_zero:\n" ++ emitProgram bnpFp2Zero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnpFp2Zero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fp2ZeroFunction_eq_prog :
    bn254Fp2ZeroFunction = "bnp_fp2_zero:\n" ++ emitProgram bnpFp2Zero_prog := rfl

#guard bn254Fp2ZeroFunction.startsWith "bnp_fp2_zero:\n"
#guard bnpFp2Zero_prog.length = 9
/-- a0 = 1 iff the two 64-byte LE Fp2 values at a0/a1 are equal (both
    reduced, so limb equality is field equality). -/
def bnpFp2Eq_prog : Program :=
  [ .LI .x5 (8 : Word),
    .BEQ .x5 .x0 (32 : BitVec 13),
    .LD .x6 .x10 (0 : BitVec 12),
    .LD .x7 .x11 (0 : BitVec 12),
    .BNE .x6 .x7 (28 : BitVec 13),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-28 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fp2EqFunction : String :=
  "bnp_fp2_eq:\n" ++ emitProgram bnpFp2Eq_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnpFp2Eq_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fp2EqFunction_eq_prog :
    bn254Fp2EqFunction = "bnp_fp2_eq:\n" ++ emitProgram bnpFp2Eq_prog := rfl

#guard bn254Fp2EqFunction.startsWith "bnp_fp2_eq:\n"
#guard bnpFp2Eq_prog.length = 13
/-- a0 = 1 iff the 64-byte LE Fp2 value at a0 is zero. -/
def bnpFp2IsZero_prog : Program :=
  [ .LI .x5 (8 : Word),
    .LI .x6 (0 : Word),
    .BEQ .x5 .x0 (24 : BitVec 13),
    .LD .x7 .x10 (0 : BitVec 12),
    .OR .x6 .x6 .x7,
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .SLTIU .x10 .x6 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254Fp2IsZeroFunction : String :=
  "bnp_fp2_is_zero:\n" ++ emitProgram bnpFp2IsZero_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnpFp2IsZero_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254Fp2IsZeroFunction_eq_prog :
    bn254Fp2IsZeroFunction = "bnp_fp2_is_zero:\n" ++ emitProgram bnpFp2IsZero_prog := rfl

#guard bn254Fp2IsZeroFunction.startsWith "bnp_fp2_is_zero:\n"
#guard bnpFp2IsZero_prog.length = 10
/-- Fp dst = a * b mod p over 32-byte LE buffers (Arith256Mod,
    d = (a*b + 0) mod p). a0 = dst, a1 = a, a2 = b; dst may alias a/b
    (the accelerator reads its inputs before writing d). Leaf; clobbers
    t0/t1. -/
def bnpFpMul_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnp_arith_params (GuestAddrs.bnp_fp_mul + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_arith_params (GuestAddrs.bnp_fp_mul + 0)),
    .SD .x5 .x11 (0 : BitVec 12),
    .SD .x5 .x12 (8 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bnf_le_zero (GuestAddrs.bnp_fp_mul + 16)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bnf_le_zero (GuestAddrs.bnp_fp_mul + 16)),
    .SD .x5 .x6 (16 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bnf_le_p (GuestAddrs.bnp_fp_mul + 28)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bnf_le_p (GuestAddrs.bnp_fp_mul + 28)),
    .SD .x5 .x6 (24 : BitVec 12),
    .SD .x5 .x10 (32 : BitVec 12),
    .CSRS (2050 : BitVec 12) .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFpMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFpMul_relocs : RelocTable :=
  [ (0, .la .x5 "bnp_arith_params"),
    (4, .la .x6 "bnf_le_zero"),
    (7, .la .x6 "bnf_le_p") ]

def bn254FpMulLeFunction : String :=
  "bnp_fp_mul:\n" ++ emitProgramR bnpFpMul_prog bnpFpMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFpMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FpMulLeFunction_eq_prog :
    bn254FpMulLeFunction = "bnp_fp_mul:\n" ++ emitProgramR bnpFpMul_prog bnpFpMul_relocs := rfl

#guard bn254FpMulLeFunction.startsWith "bnp_fp_mul:\n"
#guard bnpFpMul_prog.length = 13
/-- Fp dst = a + b mod p over 32-byte LE buffers (d = (a*1 + b) mod p).
    a0 = dst, a1 = a, a2 = b; aliasing allowed. Leaf; clobbers t0/t1. -/
def bnpFpAdd_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnp_arith_params (GuestAddrs.bnp_fp_add + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnp_arith_params (GuestAddrs.bnp_fp_add + 0)),
    .SD .x5 .x11 (0 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bnf_le_one (GuestAddrs.bnp_fp_add + 12)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bnf_le_one (GuestAddrs.bnp_fp_add + 12)),
    .SD .x5 .x6 (8 : BitVec 12),
    .SD .x5 .x12 (16 : BitVec 12),
    .AUIPC .x6 (laHi GuestAddrs.bnf_le_p (GuestAddrs.bnp_fp_add + 28)),
    .ADDI .x6 .x6 (laLo GuestAddrs.bnf_le_p (GuestAddrs.bnp_fp_add + 28)),
    .SD .x5 .x6 (24 : BitVec 12),
    .SD .x5 .x10 (32 : BitVec 12),
    .CSRS (2050 : BitVec 12) .x5,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFpAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFpAdd_relocs : RelocTable :=
  [ (0, .la .x5 "bnp_arith_params"),
    (3, .la .x6 "bnf_le_one"),
    (7, .la .x6 "bnf_le_p") ]

def bn254FpAddLeFunction : String :=
  "bnp_fp_add:\n" ++ emitProgramR bnpFpAdd_prog bnpFpAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFpAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FpAddLeFunction_eq_prog :
    bn254FpAddLeFunction = "bnp_fp_add:\n" ++ emitProgramR bnpFpAdd_prog bnpFpAdd_relocs := rfl

#guard bn254FpAddLeFunction.startsWith "bnp_fp_add:\n"
#guard bnpFpAdd_prog.length = 13
/-- Fp dst = base ^ exp mod p over 32-byte LE buffers, MSB-first
    square-and-multiply over bits 253..0 (enough for any exponent < p).
    a0 = dst, a1 = base, a2 = exp (LE limbs). dst must NOT alias base or
    exp. -/
def bnpFpPow_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .LI .x5 (1 : Word),
    .SD .x8 .x5 (0 : BitVec 12),
    .SD .x8 .x0 (8 : BitVec 12),
    .SD .x8 .x0 (16 : BitVec 12),
    .SD .x8 .x0 (24 : BitVec 12),
    .LI .x19 (253 : Word),
    .MV .x10 .x8,
    .MV .x11 .x8,
    .MV .x12 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (GuestAddrs.bnp_fp_pow + 72)),
    .SRLI .x5 .x19 (6 : BitVec 6),
    .SLLI .x5 .x5 (3 : BitVec 6),
    .ADD .x5 .x18 .x5,
    .LD .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x19 (63 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x6 .x6 (1 : BitVec 12),
    .BEQ .x6 .x0 (20 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (GuestAddrs.bnp_fp_pow + 120)),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (-72 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFpPow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFpPow_relocs : RelocTable :=
  [ (18, .jal .x1 "bnp_fp_mul"),
    (30, .jal .x1 "bnp_fp_mul") ]

def bn254FpPowLeFunction : String :=
  "bnp_fp_pow:\n" ++ emitProgramR bnpFpPow_prog bnpFpPow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFpPow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254FpPowLeFunction_eq_prog :
    bn254FpPowLeFunction = "bnp_fp_pow:\n" ++ emitProgramR bnpFpPow_prog bnpFpPow_relocs := rfl

#guard bn254FpPowLeFunction.startsWith "bnp_fp_pow:\n"
#guard bnpFpPow_prog.length = 41
/-- Fp2 inverse: dst = src^-1 = (x0 - x1 u) / (x0^2 + x1^2).
    a0 = dst, a1 = src (64-byte LE; aliasing allowed — the result is
    composed in scratch). Inverse of zero yields zero (the Fermat power
    of 0 is 0); callers gate on `bnp_fp2_is_zero` where it matters. -/
def bnpFp2Inv_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x10 (laHi bnpT0Placeholder (bnpFp2InvPc + 24)),
    .ADDI .x10 .x10 (laLo bnpT0Placeholder (bnpFp2InvPc + 24)),
    .MV .x11 .x9,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (bnpFp2InvPc + 40)),
    .AUIPC .x10 (laHi bnpT1Placeholder (bnpFp2InvPc + 44)),
    .ADDI .x10 .x10 (laLo bnpT1Placeholder (bnpFp2InvPc + 44)),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .ADDI .x12 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (bnpFp2InvPc + 60)),
    .AUIPC .x10 (laHi bnpT0Placeholder (bnpFp2InvPc + 64)),
    .ADDI .x10 .x10 (laLo bnpT0Placeholder (bnpFp2InvPc + 64)),
    .AUIPC .x11 (laHi bnpT0Placeholder (bnpFp2InvPc + 72)),
    .ADDI .x11 .x11 (laLo bnpT0Placeholder (bnpFp2InvPc + 72)),
    .AUIPC .x12 (laHi bnpT1Placeholder (bnpFp2InvPc + 80)),
    .ADDI .x12 .x12 (laLo bnpT1Placeholder (bnpFp2InvPc + 80)),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_add (bnpFp2InvPc + 88)),
    .AUIPC .x10 (laHi bnpT1Placeholder (bnpFp2InvPc + 92)),
    .ADDI .x10 .x10 (laLo bnpT1Placeholder (bnpFp2InvPc + 92)),
    .AUIPC .x11 (laHi bnpT0Placeholder (bnpFp2InvPc + 100)),
    .ADDI .x11 .x11 (laLo bnpT0Placeholder (bnpFp2InvPc + 100)),
    .AUIPC .x12 (laHi bnpPMinus2LePlaceholder (bnpFp2InvPc + 108)),
    .ADDI .x12 .x12 (laLo bnpPMinus2LePlaceholder (bnpFp2InvPc + 108)),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_pow (bnpFp2InvPc + 116)),
    .AUIPC .x10 (laHi bnpT2Placeholder (bnpFp2InvPc + 120)),
    .ADDI .x10 .x10 (laLo bnpT2Placeholder (bnpFp2InvPc + 120)),
    .MV .x11 .x9,
    .AUIPC .x12 (laHi bnpT1Placeholder (bnpFp2InvPc + 132)),
    .ADDI .x12 .x12 (laLo bnpT1Placeholder (bnpFp2InvPc + 132)),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (bnpFp2InvPc + 140)),
    .AUIPC .x10 (laHi bnpT0Placeholder (bnpFp2InvPc + 144)),
    .ADDI .x10 .x10 (laLo bnpT0Placeholder (bnpFp2InvPc + 144)),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .AUIPC .x12 (laHi bnpT1Placeholder (bnpFp2InvPc + 156)),
    .ADDI .x12 .x12 (laLo bnpT1Placeholder (bnpFp2InvPc + 156)),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (bnpFp2InvPc + 164)),
    .AUIPC .x10 (laHi bnpT0Placeholder (bnpFp2InvPc + 168)),
    .ADDI .x10 .x10 (laLo bnpT0Placeholder (bnpFp2InvPc + 168)),
    .AUIPC .x11 (laHi bnpT0Placeholder (bnpFp2InvPc + 176)),
    .ADDI .x11 .x11 (laLo bnpT0Placeholder (bnpFp2InvPc + 176)),
    .AUIPC .x12 (laHi bnpPMinus1LePlaceholder (bnpFp2InvPc + 184)),
    .ADDI .x12 .x12 (laLo bnpPMinus1LePlaceholder (bnpFp2InvPc + 184)),
    .JAL .x1 (jalOff GuestAddrs.bnp_fp_mul (bnpFp2InvPc + 192)),
    .AUIPC .x5 (laHi bnpT2Placeholder (bnpFp2InvPc + 196)),
    .ADDI .x5 .x5 (laLo bnpT2Placeholder (bnpFp2InvPc + 196)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x8 .x6 (0 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x8 .x6 (8 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x8 .x6 (16 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x8 .x6 (24 : BitVec 12),
    .AUIPC .x5 (laHi bnpT0Placeholder (bnpFp2InvPc + 236)),
    .ADDI .x5 .x5 (laLo bnpT0Placeholder (bnpFp2InvPc + 236)),
    .LD .x6 .x5 (0 : BitVec 12),
    .SD .x8 .x6 (32 : BitVec 12),
    .LD .x6 .x5 (8 : BitVec 12),
    .SD .x8 .x6 (40 : BitVec 12),
    .LD .x6 .x5 (16 : BitVec 12),
    .SD .x8 .x6 (48 : BitVec 12),
    .LD .x6 .x5 (24 : BitVec 12),
    .SD .x8 .x6 (56 : BitVec 12),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bnpFp2Inv_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bnpFp2Inv_relocs : RelocTable :=
  [ (6, .la .x10 "bnp_t0"),
    (10, .jal .x1 "bnp_fp_mul"),
    (11, .la .x10 "bnp_t1"),
    (15, .jal .x1 "bnp_fp_mul"),
    (16, .la .x10 "bnp_t0"),
    (18, .la .x11 "bnp_t0"),
    (20, .la .x12 "bnp_t1"),
    (22, .jal .x1 "bnp_fp_add"),
    (23, .la .x10 "bnp_t1"),
    (25, .la .x11 "bnp_t0"),
    (27, .la .x12 "bnp_p_minus_2_le"),
    (29, .jal .x1 "bnp_fp_pow"),
    (30, .la .x10 "bnp_t2"),
    (33, .la .x12 "bnp_t1"),
    (35, .jal .x1 "bnp_fp_mul"),
    (36, .la .x10 "bnp_t0"),
    (39, .la .x12 "bnp_t1"),
    (41, .jal .x1 "bnp_fp_mul"),
    (42, .la .x10 "bnp_t0"),
    (44, .la .x11 "bnp_t0"),
    (46, .la .x12 "bnp_p_minus_1_le"),
    (48, .jal .x1 "bnp_fp_mul"),
    (49, .la .x5 "bnp_t2"),
    (59, .la .x5 "bnp_t0") ]

def bn254Fp2InvFunction : String :=
  "bnp_fp2_inv:\n" ++ emitProgramR bnpFp2Inv_prog bnpFp2Inv_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bnpFp2Inv_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254Fp2InvFunction_eq_prog :
    bn254Fp2InvFunction = "bnp_fp2_inv:\n" ++ emitProgramR bnpFp2Inv_prog bnpFp2Inv_relocs := rfl

#guard bn254Fp2InvFunction.startsWith "bnp_fp2_inv:\n"
#guard bnpFp2Inv_prog.length = 74

/-- The Fp2 layer suite (requires `bn254FieldDataFragment` +
    `bn254Fp2DataFragment` in the data section). Guest-linked: `bnp_fp2_inv`
    unlinked (never-ref); KEEP add/sub/mul/copy/zero/eq/is_zero + Fp mul/add/pow
    LE. Probe keeps `bn254Fp2InvFunction`. -/
def bn254Fp2CommonFunctions : String :=
  bn254Fp2AddFunction ++ "\n" ++
  bn254Fp2SubFunction ++ "\n" ++
  bn254Fp2MulFunction ++ "\n" ++
  bn254Fp2CopyFunction ++ "\n" ++
  bn254Fp2ZeroFunction ++ "\n" ++
  bn254Fp2EqFunction ++ "\n" ++
  bn254Fp2IsZeroFunction ++ "\n" ++
  bn254FpMulLeFunction ++ "\n" ++
  bn254FpAddLeFunction ++ "\n" ++
  bn254FpPowLeFunction

/-- Probe: read two LE Fp2 values a (input+0) and b (input+64) and write
    a+b / a-b / a*b / a^-1 as four 64-byte LE results filling the
    256-byte output window. -/
def ziskBn254Fp2OpsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  li s1, 0xa0010000\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnp_fp2_copy\n" ++
  "  mv a0, s1\n" ++
  "  addi a1, s0, 64\n" ++
  "  jal ra, bnp_fp2_add            # out[0..64] = a + b\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s1, 64\n" ++
  "  jal ra, bnp_fp2_copy\n" ++
  "  addi a0, s1, 64\n" ++
  "  addi a1, s0, 64\n" ++
  "  jal ra, bnp_fp2_sub            # out[64..128] = a - b\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s1, 128\n" ++
  "  jal ra, bnp_fp2_copy\n" ++
  "  addi a0, s1, 128\n" ++
  "  addi a1, s0, 64\n" ++
  "  jal ra, bnp_fp2_mul            # out[128..192] = a * b\n" ++
  "  addi a0, s1, 192\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, bnp_fp2_inv            # out[192..256] = a^-1\n" ++
  "  j .Lbnp_fp2_probe_done\n" ++
  bn254Fp2CommonFunctions ++ "\n" ++
  bn254Fp2InvFunction ++ "\n" ++
  ".Lbnp_fp2_probe_done:"


end EvmAsm.Codegen
