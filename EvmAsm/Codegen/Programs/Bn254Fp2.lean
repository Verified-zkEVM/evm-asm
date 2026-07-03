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
import EvmAsm.Codegen.Programs.Bn254Field

namespace EvmAsm.Codegen

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
def bn254Fp2AddFunction : String :=
  "bnp_fp2_add:\n" ++
  "  la t0, bnp_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  .4byte 0x8082a073             # csrs 0x808, t0 -> Bn254ComplexAdd\n" ++
  "  ret"

/-- Fp2 dst -= src. Leaf; clobbers t0. -/
def bn254Fp2SubFunction : String :=
  "bnp_fp2_sub:\n" ++
  "  la t0, bnp_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  .4byte 0x8092a073             # csrs 0x809, t0 -> Bn254ComplexSub\n" ++
  "  ret"

/-- Fp2 dst *= src ((x0 + x1 u)(y0 + y1 u), u^2 = -1). Leaf; clobbers t0. -/
def bn254Fp2MulFunction : String :=
  "bnp_fp2_mul:\n" ++
  "  la t0, bnp_cplx_params\n" ++
  "  sd a0, 0(t0)\n" ++
  "  sd a1, 8(t0)\n" ++
  "  .4byte 0x80a2a073             # csrs 0x80A, t0 -> Bn254ComplexMul\n" ++
  "  ret"

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
def bn254FpMulLeFunction : String :=
  "bnp_fp_mul:\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  sd a1, 0(t0)\n" ++
  "  sd a2, 8(t0)\n" ++
  "  la t1, bnf_le_zero\n" ++
  "  sd t1, 16(t0)\n" ++
  "  la t1, bnf_le_p\n" ++
  "  sd t1, 24(t0)\n" ++
  "  sd a0, 32(t0)\n" ++
  "  .4byte 0x8022a073             # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  ret"

/-- Fp dst = a + b mod p over 32-byte LE buffers (d = (a*1 + b) mod p).
    a0 = dst, a1 = a, a2 = b; aliasing allowed. Leaf; clobbers t0/t1. -/
def bn254FpAddLeFunction : String :=
  "bnp_fp_add:\n" ++
  "  la t0, bnp_arith_params\n" ++
  "  sd a1, 0(t0)\n" ++
  "  la t1, bnf_le_one\n" ++
  "  sd t1, 8(t0)\n" ++
  "  sd a2, 16(t0)\n" ++
  "  la t1, bnf_le_p\n" ++
  "  sd t1, 24(t0)\n" ++
  "  sd a0, 32(t0)\n" ++
  "  .4byte 0x8022a073             # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  ret"

/-- Fp dst = base ^ exp mod p over 32-byte LE buffers, MSB-first
    square-and-multiply over bits 253..0 (enough for any exponent < p).
    a0 = dst, a1 = base, a2 = exp (LE limbs). dst must NOT alias base or
    exp. -/
def bn254FpPowLeFunction : String :=
  "bnp_fp_pow:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(s0)\n" ++
  "  sd zero, 8(s0)\n" ++
  "  sd zero, 16(s0)\n" ++
  "  sd zero, 24(s0)\n" ++
  "  li s3, 253                     # bit index\n" ++
  ".Lbnp_pow_loop:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s0\n" ++
  "  jal ra, bnp_fp_mul             # dst = dst^2\n" ++
  "  srli t0, s3, 6\n" ++
  "  slli t0, t0, 3\n" ++
  "  add t0, s2, t0\n" ++
  "  ld t1, 0(t0)\n" ++
  "  andi t2, s3, 63\n" ++
  "  srl t1, t1, t2\n" ++
  "  andi t1, t1, 1\n" ++
  "  beqz t1, .Lbnp_pow_skip\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, bnp_fp_mul             # dst *= base\n" ++
  ".Lbnp_pow_skip:\n" ++
  "  beqz s3, .Lbnp_pow_done\n" ++
  "  addi s3, s3, -1\n" ++
  "  j .Lbnp_pow_loop\n" ++
  ".Lbnp_pow_done:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Fp2 inverse: dst = src^-1 = (x0 - x1 u) / (x0^2 + x1^2).
    a0 = dst, a1 = src (64-byte LE; aliasing allowed — the result is
    composed in scratch). Inverse of zero yields zero (the Fermat power
    of 0 is 0); callers gate on `bnp_fp2_is_zero` where it matters. -/
def bn254Fp2InvFunction : String :=
  "bnp_fp2_inv:\n" ++
  "  addi sp, sp, -24\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  la a0, bnp_t0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, bnp_fp_mul             # t0 = x0^2\n" ++
  "  la a0, bnp_t1\n" ++
  "  addi a1, s1, 32\n" ++
  "  addi a2, s1, 32\n" ++
  "  jal ra, bnp_fp_mul             # t1 = x1^2\n" ++
  "  la a0, bnp_t0\n" ++
  "  la a1, bnp_t0\n" ++
  "  la a2, bnp_t1\n" ++
  "  jal ra, bnp_fp_add             # t0 = x0^2 + x1^2\n" ++
  "  la a0, bnp_t1\n" ++
  "  la a1, bnp_t0\n" ++
  "  la a2, bnp_p_minus_2_le\n" ++
  "  jal ra, bnp_fp_pow             # t1 = norm^(p-2)\n" ++
  "  la a0, bnp_t2\n" ++
  "  mv a1, s1\n" ++
  "  la a2, bnp_t1\n" ++
  "  jal ra, bnp_fp_mul             # t2 = x0 / norm\n" ++
  "  la a0, bnp_t0\n" ++
  "  addi a1, s1, 32\n" ++
  "  la a2, bnp_t1\n" ++
  "  jal ra, bnp_fp_mul             # t0 = x1 / norm\n" ++
  "  la a0, bnp_t0\n" ++
  "  la a1, bnp_t0\n" ++
  "  la a2, bnp_p_minus_1_le\n" ++
  "  jal ra, bnp_fp_mul             # t0 = -x1 / norm\n" ++
  "  la t0, bnp_t2\n" ++
  "  ld t1, 0(t0);  sd t1,  0(s0)\n" ++
  "  ld t1, 8(t0);  sd t1,  8(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 16(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 24(s0)\n" ++
  "  la t0, bnp_t0\n" ++
  "  ld t1, 0(t0);  sd t1, 32(s0)\n" ++
  "  ld t1, 8(t0);  sd t1, 40(s0)\n" ++
  "  ld t1, 16(t0); sd t1, 48(s0)\n" ++
  "  ld t1, 24(t0); sd t1, 56(s0)\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 24\n" ++
  "  ret"

/-- The Fp2 layer suite (requires `bn254FieldDataFragment` +
    `bn254Fp2DataFragment` in the data section). -/
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
  bn254FpPowLeFunction ++ "\n" ++
  bn254Fp2InvFunction

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
  ".Lbnp_fp2_probe_done:"

def ziskBn254Fp2OpsProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBn254Fp2OpsProbePrologue
  dataAsm     := bn254Fp2DataSection
}

end EvmAsm.Codegen
