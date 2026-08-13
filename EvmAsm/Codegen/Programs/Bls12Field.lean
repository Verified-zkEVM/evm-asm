/-
  EvmAsm.Codegen.Programs.Bls12Field

  BLS12-381 base layer for the EIP-2537 precompiles (0x0b..0x11):
  the ziskemu accelerator bindings, base-field constants, and the
  standalone accelerator probe.

  The installed ziskemu (0.16.0) implements FIVE BLS12-381-relevant
  syscalls (the older in-tree "ziskemu safe-fails the BLS wrappers"
  comments predate this; see /tmp/zisk definitions/src/syscall.rs):

    * Arith384Mod        csrs 0x80B  (.4byte 0x80b52073, a0 = param ptr)
        param = {&a, &b, &c, &module, &d}; d = (a*b + c) mod module,
        exact 768-bit intermediate, all values 6 LE u64 limbs (48 B).
    * Bls12_381CurveAdd  csrs 0x80C  (.4byte 0x80c52073)
        param = {&p1, &p2}; p1 += p2 (affine chord; requires x1 != x2,
        like the BN254/secp256k1 curve accelerators — infinity, equal-x
        and doubling are software-handled by the wrappers).
    * Bls12_381CurveDbl  csrs 0x80D  (.4byte 0x80d52073)
        param = &p1; p1 = 2*p1 (affine tangent; y != 0 required).
    * Bls12_381ComplexAdd/Sub/Mul  csrs 0x80E/0x80F/0x810
        (.4byte 0x80e52073 / 0x80f52073 / 0x81052073)
        param = {&f1, &f2}; f1 ◦= f2 over Fp2 = Fp[u]/(u^2 + 1);
        elements are 96-byte buffers: c0 limbs at +0, c1 limbs at +48.

  Points are `SyscallPoint384`: x limbs LSB-first at +0, y at +48
  (96-byte, 8-aligned). The whole BLS tower stays in this native LE
  format; big-endian conversions happen only at the EIP-2537 input /
  output boundary (mirroring the BN254 design that landed in
  Bn254Field/Bn254Fp2).

  All labels are `blsf_`-prefixed so closures can link this chain next
  to the BN254 (`bnf_`/`bnp_`) and secp256k1 (`secf_`) chains without
  label clashes.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.GuestAddrs

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- BLS12-381 base-field data labels WITHOUT a `.section .data` header,
    for appending to an existing data section. Constants + accelerator
    staging buffers + the three static parameter blocks. -/
def bls12FieldDataFragment : String :=
  ".balign 8\n" ++
  -- p = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf
  --     6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab (LE limbs)
  "blsf_le_p:\n" ++
  "  .quad 0xb9feffffffffaaab, 0x1eabfffeb153ffff\n" ++
  "  .quad 0x6730d2a0f6b0f624, 0x64774b84f38512bf\n" ++
  "  .quad 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a\n" ++
  "blsf_le_zero:\n" ++
  "  .zero 48\n" ++
  "blsf_le_one:\n" ++
  "  .quad 1, 0, 0, 0, 0, 0\n" ++
  -- Arith384Mod staging cells + {a, b, c, module, d} parameter block
  -- (mul: c = blsf_le_zero; add: b = blsf_le_one with addend in c).
  "blsf_le_a:\n  .zero 48\n" ++
  "blsf_le_b:\n  .zero 48\n" ++
  "blsf_le_d:\n  .zero 48\n" ++
  "blsf_mul_params:\n" ++
  "  .quad blsf_le_a, blsf_le_b, blsf_le_zero, blsf_le_p, blsf_le_d\n" ++
  "blsf_add_params:\n" ++
  "  .quad blsf_le_a, blsf_le_one, blsf_le_b, blsf_le_p, blsf_le_d\n" ++
  -- Curve accelerator staging points + {p1, p2} parameter block.
  "blsf_p1:\n  .zero 96\n" ++
  "blsf_p2:\n  .zero 96\n" ++
  "blsf_curve_params:\n" ++
  "  .quad blsf_p1, blsf_p2\n" ++
  -- Fp2 staging + {f1, f2} parameter block for the complex accelerators.
  "blsf_f1:\n  .zero 96\n" ++
  "blsf_f2:\n  .zero 96\n" ++
  "blsf_cplx_params:\n" ++
  "  .quad blsf_f1, blsf_f2\n"

/-- Standalone `.data` section for focused probes. -/
def bls12FieldDataSection : String :=
  ".section .data\n" ++ bls12FieldDataFragment

/-- Copy 8-byte quads: a0 = src, a1 = dst (both 8-aligned), a2 = quad
    count. Leaf; clobbers t0, a0, a1, a2. -/
def blsfCopyQuads_prog : Program :=
  [ .BEQ .x12 .x0 (28 : BitVec 13),
    .LD .x5 .x10 (0 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x11 .x11 (8 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bls12CopyQuadsFunction : String :=
  "blsf_copy_quads:\n" ++ emitProgram blsfCopyQuads_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `blsfCopyQuads_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bls12CopyQuadsFunction_eq_prog :
    bls12CopyQuadsFunction = "blsf_copy_quads:\n" ++ emitProgram blsfCopyQuads_prog := rfl

#guard bls12CopyQuadsFunction.startsWith "blsf_copy_quads:\n"
#guard blsfCopyQuads_prog.length = 8
/-- Fp d = (a*b) mod p: a0/a1 = 48-byte LE inputs (copied into the
    staging cells), result left in `blsf_le_d`. Clobbers t0, a0..a2, ra
    is preserved via stack. -/
def blsfFpMul_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x11 (8 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_a 2147483660),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_a 2147483660),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads 2147483672),
    .LD .x10 .x2 (8 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_b 2147483680),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_b 2147483680),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads 2147483692),
    .AUIPC .x10 (laHi GuestAddrs.blsf_mul_params 2147483696),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_mul_params 2147483696),
    .CSRS (2059 : BitVec 12) .x10,
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsfFpMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsfFpMul_relocs : RelocTable :=
  [ (3, .la .x11 "blsf_le_a"),
    (6, .jal .x1 "blsf_copy_quads"),
    (8, .la .x11 "blsf_le_b"),
    (11, .jal .x1 "blsf_copy_quads"),
    (12, .la .x10 "blsf_mul_params") ]

def bls12FpMulFunction : String :=
  "blsf_fp_mul:\n" ++ emitProgramR blsfFpMul_prog blsfFpMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsfFpMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12FpMulFunction_eq_prog :
    bls12FpMulFunction = "blsf_fp_mul:\n" ++ emitProgramR blsfFpMul_prog blsfFpMul_relocs := rfl

#guard bls12FpMulFunction.startsWith "blsf_fp_mul:\n"
#guard blsfFpMul_prog.length = 18
/-- Fp d = (a + b) mod p: same staging convention as `blsf_fp_mul`. -/
def blsfFpAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x11 (8 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_a 2147483660),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_a 2147483660),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads 2147483672),
    .LD .x10 .x2 (8 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsf_le_b 2147483680),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsf_le_b 2147483680),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads 2147483692),
    .AUIPC .x10 (laHi GuestAddrs.blsf_add_params 2147483696),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_add_params 2147483696),
    .CSRS (2059 : BitVec 12) .x10,
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsfFpAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsfFpAdd_relocs : RelocTable :=
  [ (3, .la .x11 "blsf_le_a"),
    (6, .jal .x1 "blsf_copy_quads"),
    (8, .la .x11 "blsf_le_b"),
    (11, .jal .x1 "blsf_copy_quads"),
    (12, .la .x10 "blsf_add_params") ]

def bls12FpAddFunction : String :=
  "blsf_fp_add:\n" ++ emitProgramR blsfFpAdd_prog blsfFpAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsfFpAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12FpAddFunction_eq_prog :
    bls12FpAddFunction = "blsf_fp_add:\n" ++ emitProgramR blsfFpAdd_prog blsfFpAdd_relocs := rfl

#guard bls12FpAddFunction.startsWith "blsf_fp_add:\n"
#guard blsfFpAdd_prog.length = 18
/-- Probe: exercise all five BLS12-381 ziskemu accelerators on
    host-supplied vectors and dump the raw results, so the check script
    can compare against a pure-Python reference (and so a future ziskemu
    regression is caught by a syscall-level test, not an EEST row).

    ziskemu's `-o` dump is capped at ZISK_PUBLICS = 256 bytes, so the
    probe is mode-split (three runs, mode word first).

    Input at `0x40000008` (all values LE limbs):

      +0    mode (u64: 0 curve, 1 arith+cplx add/sub, 2 cplx mul)
      +8    P1 (96 B affine x||y)        +104  P2 (96 B)
      +200  a (48 B)   +248  b (48 B)    +296  c (48 B)
      +344  F1 (96 B Fp2 c0||c1)         +440  F2 (96 B)

    Output at `0xa0010000`:

      mode 0: +0 curve_add(P1, P2) (96 B), +96 curve_dbl(P1) (96 B)
      mode 1: +0 (a*b + c) mod p (48 B), +48 F1 + F2 (96 B),
              +144 F1 - F2 (96 B)
      mode 2: +0 F1 * F2 (96 B)
-/
def ziskBls12AccelOpsProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  li s1, 0xa0010000\n" ++
  "  ld s2, 0(s0)\n" ++
  "  addi s0, s0, 8\n" ++
  "  li t0, 1\n" ++
  "  beq s2, t0, .Lblsf_probe_mode1\n" ++
  "  li t0, 2\n" ++
  "  beq s2, t0, .Lblsf_probe_mode2\n" ++
  -- mode 0 — curve add: stage P1/P2, fire 0x80C (result overwrites
  -- blsf_p1), then restage P1 and fire 0x80D (in place)
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  li a2, 24\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_curve_params\n" ++
  "  .4byte 0x80c52073             # csrs 0x80C, a0 -> Bls12_381CurveAdd\n" ++
  "  la a0, blsf_p1\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  mv a0, s0\n" ++
  "  la a1, blsf_p1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_p1\n" ++
  "  .4byte 0x80d52073             # csrs 0x80D, a0 -> Bls12_381CurveDbl\n" ++
  "  la a0, blsf_p1\n" ++
  "  addi a1, s1, 96\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  j .Lblsf_probe_done\n" ++
  -- mode 1 — arith384mod d = (a*b + c) mod p via the probe-only params
  -- block (a dedicated c cell keeps blsf_le_zero intact), then complex
  -- add and sub (F1 restaged before each op)
  ".Lblsf_probe_mode1:\n" ++
  "  addi a0, s0, 192\n" ++
  "  la a1, blsf_le_a\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 240\n" ++
  "  la a1, blsf_le_b\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 288\n" ++
  "  la a1, blsf_probe_c\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_probe_arith_params\n" ++
  "  .4byte 0x80b52073             # csrs 0x80B, a0 -> Arith384Mod\n" ++
  "  la a0, blsf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 6\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 432\n" ++
  "  la a1, blsf_f2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 336\n" ++
  "  la a1, blsf_f1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_cplx_params\n" ++
  "  .4byte 0x80e52073             # csrs 0x80E, a0 -> Bls12_381ComplexAdd\n" ++
  "  la a0, blsf_f1\n" ++
  "  addi a1, s1, 48\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 336\n" ++
  "  la a1, blsf_f1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_cplx_params\n" ++
  "  .4byte 0x80f52073             # csrs 0x80F, a0 -> Bls12_381ComplexSub\n" ++
  "  la a0, blsf_f1\n" ++
  "  addi a1, s1, 144\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  j .Lblsf_probe_done\n" ++
  -- mode 2 — complex mul
  ".Lblsf_probe_mode2:\n" ++
  "  addi a0, s0, 432\n" ++
  "  la a1, blsf_f2\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  addi a0, s0, 336\n" ++
  "  la a1, blsf_f1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  la a0, blsf_cplx_params\n" ++
  "  .4byte 0x81052073             # csrs 0x810, a0 -> Bls12_381ComplexMul\n" ++
  "  la a0, blsf_f1\n" ++
  "  mv a1, s1\n" ++
  "  li a2, 12\n" ++
  "  jal ra, blsf_copy_quads\n" ++
  "  j .Lblsf_probe_done\n" ++
  bls12CopyQuadsFunction ++ "\n" ++
  ".Lblsf_probe_done:"

/-- Probe-only data: a dedicated c cell + arith params block so the
    probe can exercise the fused add term without disturbing the
    shared `blsf_le_zero` constant. -/
def ziskBls12AccelOpsProbeDataSection : String :=
  bls12FieldDataSection ++
  "blsf_probe_c:\n  .zero 48\n" ++
  "blsf_probe_arith_params:\n" ++
  "  .quad blsf_le_a, blsf_le_b, blsf_probe_c, blsf_le_p, blsf_le_d\n"


end EvmAsm.Codegen
