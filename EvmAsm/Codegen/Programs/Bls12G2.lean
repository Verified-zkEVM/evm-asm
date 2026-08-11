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
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bls12G1
import EvmAsm.Codegen.Programs.Bls12G2EqNSAsm

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
def blsg2FpMul_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsg2_fp_params (GuestAddrs.blsg2_fp_mul + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsg2_fp_params (GuestAddrs.blsg2_fp_mul + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_zero (GuestAddrs.blsg2_fp_mul + 16)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_zero (GuestAddrs.blsg2_fp_mul + 16)),
    .SD .x5 .x10 (16 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_p (GuestAddrs.blsg2_fp_mul + 28)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_p (GuestAddrs.blsg2_fp_mul + 28)),
    .SD .x5 .x10 (24 : BitVec 12),
    .SD .x5 .x12 (32 : BitVec 12),
    .MV .x10 .x5,
    .CSRS (2059 : BitVec 12) .x10,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2FpMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2FpMul_relocs : RelocTable :=
  [ (0, .la .x5 "blsg2_fp_params"),
    (4, .la .x10 "blsf_le_zero"),
    (7, .la .x10 "blsf_le_p") ]

def bls12G2FpMulLeFunction : String :=
  "blsg2_fp_mul:\n" ++ emitProgramR blsg2FpMul_prog blsg2FpMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2FpMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2FpMulLeFunction_eq_prog :
    bls12G2FpMulLeFunction = "blsg2_fp_mul:\n" ++ emitProgramR blsg2FpMul_prog blsg2FpMul_relocs := rfl

#guard bls12G2FpMulLeFunction.startsWith "blsg2_fp_mul:\n"
#guard blsg2FpMul_prog.length = 14
/-- Fp d = (a + b) mod p on LE cells (d = a*1 + b). Leaf; clobbers t0, a0. -/
def blsg2FpAdd_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsg2_fp_params (GuestAddrs.blsg2_fp_add + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsg2_fp_params (GuestAddrs.blsg2_fp_add + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_one (GuestAddrs.blsg2_fp_add + 12)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_one (GuestAddrs.blsg2_fp_add + 12)),
    .SD .x5 .x10 (8 : BitVec 12),
    .SD .x5 .x11 (16 : BitVec 12),
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_p (GuestAddrs.blsg2_fp_add + 28)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_p (GuestAddrs.blsg2_fp_add + 28)),
    .SD .x5 .x10 (24 : BitVec 12),
    .SD .x5 .x12 (32 : BitVec 12),
    .MV .x10 .x5,
    .CSRS (2059 : BitVec 12) .x10,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2FpAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2FpAdd_relocs : RelocTable :=
  [ (0, .la .x5 "blsg2_fp_params"),
    (3, .la .x10 "blsf_le_one"),
    (7, .la .x10 "blsf_le_p") ]

def bls12G2FpAddLeFunction : String :=
  "blsg2_fp_add:\n" ++ emitProgramR blsg2FpAdd_prog blsg2FpAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2FpAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2FpAddLeFunction_eq_prog :
    bls12G2FpAddLeFunction = "blsg2_fp_add:\n" ++ emitProgramR blsg2FpAdd_prog blsg2FpAdd_relocs := rfl

#guard bls12G2FpAddLeFunction.startsWith "blsg2_fp_add:\n"
#guard blsg2FpAdd_prog.length = 14
/-- Fp d = a^(p-2) mod p (Fermat inverse; a reduced, nonzero) on LE
    cells: a0 = a, a1 = d (must NOT alias a or `blsg2_facc`). -/
def blsg2FpInv_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x10 (laHi GuestAddrs.blsf_le_one (GuestAddrs.blsg2_fp_inv + 36)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsf_le_one (GuestAddrs.blsg2_fp_inv + 36)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 44)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 44)),
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_fp_inv + 56)),
    .LI .x18 (0 : Word),
    .LI .x5 (48 : Word),
    .BGEU .x18 .x5 (brOff (GuestAddrs.blsg2_fp_inv + 172) (GuestAddrs.blsg2_fp_inv + 68)),
    .AUIPC .x5 (laHi GuestAddrs.blsg2_p_minus_2_be (GuestAddrs.blsg2_fp_inv + 72)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsg2_p_minus_2_be (GuestAddrs.blsg2_fp_inv + 72)),
    .ADD .x5 .x5 .x18,
    .LBU .x19 .x5 (0 : BitVec 12),
    .LI .x20 (128 : Word),
    .BEQ .x20 .x0 (brOff (GuestAddrs.blsg2_fp_inv + 164) (GuestAddrs.blsg2_fp_inv + 92)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 96)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 96)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 104)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 104)),
    .AUIPC .x12 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 112)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 112)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp_inv + 120)),
    .AND .x5 .x19 .x20,
    .BEQ .x5 .x0 (28 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 132)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 144)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp_inv + 152)),
    .SRLI .x20 .x20 (1 : BitVec 6),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_fp_inv + 92) (GuestAddrs.blsg2_fp_inv + 160)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_fp_inv + 64) (GuestAddrs.blsg2_fp_inv + 168)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_facc (GuestAddrs.blsg2_fp_inv + 172)),
    .MV .x11 .x9,
    .LI .x12 (6 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_fp_inv + 188)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2FpInv_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2FpInv_relocs : RelocTable :=
  [ (9, .la .x10 "blsf_le_one"),
    (11, .la .x11 "blsg2_facc"),
    (14, .jal .x1 "blsf_copy_quads"),
    (18, .la .x5 "blsg2_p_minus_2_be"),
    (24, .la .x10 "blsg2_facc"),
    (26, .la .x11 "blsg2_facc"),
    (28, .la .x12 "blsg2_facc"),
    (30, .jal .x1 "blsg2_fp_mul"),
    (33, .la .x10 "blsg2_facc"),
    (36, .la .x12 "blsg2_facc"),
    (38, .jal .x1 "blsg2_fp_mul"),
    (43, .la .x10 "blsg2_facc"),
    (47, .jal .x1 "blsf_copy_quads") ]

def bls12G2FpInvFunction : String :=
  "blsg2_fp_inv:\n" ++ emitProgramR blsg2FpInv_prog blsg2FpInv_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2FpInv_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2FpInvFunction_eq_prog :
    bls12G2FpInvFunction = "blsg2_fp_inv:\n" ++ emitProgramR blsg2FpInv_prog blsg2FpInv_relocs := rfl

#guard bls12G2FpInvFunction.startsWith "blsg2_fp_inv:\n"
#guard blsg2FpInv_prog.length = 56
/-- Fp2 dst += src (96-byte LE buffers). Leaf; clobbers t0, a0. -/
def blsg2Fp2Add_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_add + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_add + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .MV .x10 .x5,
    .CSRS (2062 : BitVec 12) .x10,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Fp2Add_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Fp2Add_relocs : RelocTable :=
  [ (0, .la .x5 "blsf_cplx_params") ]

def bls12G2Fp2AddFunction : String :=
  "blsg2_fp2_add:\n" ++ emitProgramR blsg2Fp2Add_prog blsg2Fp2Add_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Fp2Add_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2Fp2AddFunction_eq_prog :
    bls12G2Fp2AddFunction = "blsg2_fp2_add:\n" ++ emitProgramR blsg2Fp2Add_prog blsg2Fp2Add_relocs := rfl

#guard bls12G2Fp2AddFunction.startsWith "blsg2_fp2_add:\n"
#guard blsg2Fp2Add_prog.length = 7
/-- Fp2 dst -= src. Leaf; clobbers t0, a0. -/
def blsg2Fp2Sub_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_sub + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_sub + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .MV .x10 .x5,
    .CSRS (2063 : BitVec 12) .x10,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Fp2Sub_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Fp2Sub_relocs : RelocTable :=
  [ (0, .la .x5 "blsf_cplx_params") ]

def bls12G2Fp2SubFunction : String :=
  "blsg2_fp2_sub:\n" ++ emitProgramR blsg2Fp2Sub_prog blsg2Fp2Sub_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Fp2Sub_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2Fp2SubFunction_eq_prog :
    bls12G2Fp2SubFunction = "blsg2_fp2_sub:\n" ++ emitProgramR blsg2Fp2Sub_prog blsg2Fp2Sub_relocs := rfl

#guard bls12G2Fp2SubFunction.startsWith "blsg2_fp2_sub:\n"
#guard blsg2Fp2Sub_prog.length = 7
/-- Fp2 dst *= src (u^2 = -1). Leaf; clobbers t0, a0. -/
def blsg2Fp2Mul_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_mul + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.blsf_cplx_params (GuestAddrs.blsg2_fp2_mul + 0)),
    .SD .x5 .x10 (0 : BitVec 12),
    .SD .x5 .x11 (8 : BitVec 12),
    .MV .x10 .x5,
    .CSRS (2064 : BitVec 12) .x10,
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Fp2Mul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Fp2Mul_relocs : RelocTable :=
  [ (0, .la .x5 "blsf_cplx_params") ]

def bls12G2Fp2MulFunction : String :=
  "blsg2_fp2_mul:\n" ++ emitProgramR blsg2Fp2Mul_prog blsg2Fp2Mul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Fp2Mul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2Fp2MulFunction_eq_prog :
    bls12G2Fp2MulFunction = "blsg2_fp2_mul:\n" ++ emitProgramR blsg2Fp2Mul_prog blsg2Fp2Mul_relocs := rfl

#guard bls12G2Fp2MulFunction.startsWith "blsg2_fp2_mul:\n"
#guard blsg2Fp2Mul_prog.length = 7
/-- Fp2 inverse: a0 = src (96 B LE, nonzero), a1 = dst (must not alias
    src). (c0 + c1 u)^-1 = (c0 - c1 u) / (c0^2 + c1^2). -/
def blsg2Fp2Inv_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 32)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 32)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp2_inv + 40)),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .ADDI .x11 .x8 (48 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 52)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 52)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp2_inv + 60)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 64)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 72)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 72)),
    .AUIPC .x12 (laHi GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 80)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 80)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_add (GuestAddrs.blsg2_fp2_inv + 88)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 92)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_n (GuestAddrs.blsg2_fp2_inv + 92)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 100)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 100)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_inv (GuestAddrs.blsg2_fp2_inv + 108)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 116)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 116)),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp2_inv + 128)),
    .ADDI .x10 .x8 (48 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 136)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_ninv (GuestAddrs.blsg2_fp2_inv + 136)),
    .AUIPC .x12 (laHi GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 144)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp2_inv + 152)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 156)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_ft (GuestAddrs.blsg2_fp2_inv + 156)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_pm1_le (GuestAddrs.blsg2_fp2_inv + 164)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_pm1_le (GuestAddrs.blsg2_fp2_inv + 164)),
    .ADDI .x12 .x9 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp_mul (GuestAddrs.blsg2_fp2_inv + 176)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Fp2Inv_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Fp2Inv_relocs : RelocTable :=
  [ (8, .la .x12 "blsg2_n"),
    (10, .jal .x1 "blsg2_fp_mul"),
    (13, .la .x12 "blsg2_ft"),
    (15, .jal .x1 "blsg2_fp_mul"),
    (16, .la .x10 "blsg2_n"),
    (18, .la .x11 "blsg2_ft"),
    (20, .la .x12 "blsg2_n"),
    (22, .jal .x1 "blsg2_fp_add"),
    (23, .la .x10 "blsg2_n"),
    (25, .la .x11 "blsg2_ninv"),
    (27, .jal .x1 "blsg2_fp_inv"),
    (29, .la .x11 "blsg2_ninv"),
    (32, .jal .x1 "blsg2_fp_mul"),
    (34, .la .x11 "blsg2_ninv"),
    (36, .la .x12 "blsg2_ft"),
    (38, .jal .x1 "blsg2_fp_mul"),
    (39, .la .x10 "blsg2_ft"),
    (41, .la .x11 "blsg2_pm1_le"),
    (44, .jal .x1 "blsg2_fp_mul") ]

def bls12G2Fp2InvFunction : String :=
  "blsg2_fp2_inv:\n" ++ emitProgramR blsg2Fp2Inv_prog blsg2Fp2Inv_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Fp2Inv_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2Fp2InvFunction_eq_prog :
    bls12G2Fp2InvFunction = "blsg2_fp2_inv:\n" ++ emitProgramR blsg2Fp2Inv_prog blsg2Fp2Inv_relocs := rfl

#guard bls12G2Fp2InvFunction.startsWith "blsg2_fp2_inv:\n"
#guard blsg2Fp2Inv_prog.length = 50
/-- Copy 192 bytes of 8-aligned LE point data: a0 = src, a1 = dst. -/
def blsg2Copy192_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .LI .x12 (24 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_copy192 + 12)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Copy192_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Copy192_relocs : RelocTable :=
  [ (3, .jal .x1 "blsf_copy_quads") ]

def bls12G2Copy192Function : String :=
  "blsg2_copy192:\n" ++ emitProgramR blsg2Copy192_prog blsg2Copy192_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Copy192_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2Copy192Function_eq_prog :
    bls12G2Copy192Function = "blsg2_copy192:\n" ++ emitProgramR blsg2Copy192_prog blsg2Copy192_relocs := rfl

#guard bls12G2Copy192Function.startsWith "blsg2_copy192:\n"
#guard blsg2Copy192_prog.length = 7
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
/-- a0 = 1 iff the two a2-byte buffers at a0/a1 are equal. Leaf.

    Re-emitted drop-in: the verified `Bls12G2EqNSAsm.blsg2EqNBody`
    flatten + `ret` (15 instructions, same length as the pre-drop-in two-exit compare). -/
def blsg2EqN_prog : Program :=
  Bls12G2EqNSAsm.blsg2EqN_prog

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
def blsg2ChordTail_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 32)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 32)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 40)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_chord_tail + 52)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 56)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 56)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 64)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 64)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_chord_tail + 72)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 76)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 76)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_chord_tail + 88)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 92)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 92)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_chord_tail + 104)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 112)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 112)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_chord_tail + 124)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 128)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 128)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 136)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 136)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_chord_tail + 144)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 148)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 148)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 156)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_chord_tail + 156)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_chord_tail + 164)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 168)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 168)),
    .ADDI .x11 .x8 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_chord_tail + 180)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t1 (GuestAddrs.blsg2_chord_tail + 184)),
    .MV .x11 .x18,
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_chord_tail + 200)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 204)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_t2 (GuestAddrs.blsg2_chord_tail + 204)),
    .ADDI .x11 .x18 (96 : BitVec 12),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_chord_tail + 220)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2ChordTail_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2ChordTail_relocs : RelocTable :=
  [ (8, .la .x10 "blsg2_lam"),
    (10, .la .x11 "blsg2_t1"),
    (13, .jal .x1 "blsf_copy_quads"),
    (14, .la .x10 "blsg2_t1"),
    (16, .la .x11 "blsg2_lam"),
    (18, .jal .x1 "blsg2_fp2_mul"),
    (19, .la .x10 "blsg2_t1"),
    (22, .jal .x1 "blsg2_fp2_sub"),
    (23, .la .x10 "blsg2_t1"),
    (26, .jal .x1 "blsg2_fp2_sub"),
    (28, .la .x11 "blsg2_t2"),
    (31, .jal .x1 "blsf_copy_quads"),
    (32, .la .x10 "blsg2_t2"),
    (34, .la .x11 "blsg2_t1"),
    (36, .jal .x1 "blsg2_fp2_sub"),
    (37, .la .x10 "blsg2_t2"),
    (39, .la .x11 "blsg2_lam"),
    (41, .jal .x1 "blsg2_fp2_mul"),
    (42, .la .x10 "blsg2_t2"),
    (45, .jal .x1 "blsg2_fp2_sub"),
    (46, .la .x10 "blsg2_t1"),
    (50, .jal .x1 "blsf_copy_quads"),
    (51, .la .x10 "blsg2_t2"),
    (55, .jal .x1 "blsf_copy_quads") ]

def bls12G2ChordTailFunction : String :=
  "blsg2_chord_tail:\n" ++ emitProgramR blsg2ChordTail_prog blsg2ChordTail_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2ChordTail_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2ChordTailFunction_eq_prog :
    bls12G2ChordTailFunction = "blsg2_chord_tail:\n" ++ emitProgramR blsg2ChordTail_prog blsg2ChordTail_relocs := rfl

#guard bls12G2ChordTailFunction.startsWith "blsg2_chord_tail:\n"
#guard blsg2ChordTail_prog.length = 62
/-- Double an affine LE point: a0 = input, a1 = output (192 B LE, may
    alias). Returns a0 = 1 when the result is infinity (input infinity
    or y = 0; output zeroed), else 0. -/
def blsg2PointDbl_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (96 : BitVec 12),
    .LI .x11 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_point_dbl + 32)),
    .BNE .x10 .x0 (brOff (GuestAddrs.blsg2_point_dbl + 240) (GuestAddrs.blsg2_point_dbl + 36)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 44)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 44)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_point_dbl + 56)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 60)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_point_dbl + 72)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 76)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 76)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 84)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 84)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_point_dbl + 96)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 100)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 108)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 108)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_add (GuestAddrs.blsg2_point_dbl + 116)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 120)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 120)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 128)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 128)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_add (GuestAddrs.blsg2_point_dbl + 136)),
    .ADDI .x10 .x8 (96 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 144)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 144)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_point_dbl + 156)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 160)),
    .ADDI .x11 .x8 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_add (GuestAddrs.blsg2_point_dbl + 172)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 176)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_dbl + 176)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_dbl + 184)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_dbl + 184)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_inv (GuestAddrs.blsg2_point_dbl + 192)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 196)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_dbl + 196)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_dbl + 204)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_dbl + 204)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_point_dbl + 212)),
    .MV .x10 .x8,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_chord_tail (GuestAddrs.blsg2_point_dbl + 228)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_zero192 (GuestAddrs.blsg2_point_dbl + 244)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2PointDbl_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2PointDbl_relocs : RelocTable :=
  [ (8, .jal .x1 "blsg_is_zero_n"),
    (11, .la .x11 "blsg2_lam"),
    (14, .jal .x1 "blsf_copy_quads"),
    (15, .la .x10 "blsg2_lam"),
    (18, .jal .x1 "blsg2_fp2_mul"),
    (19, .la .x10 "blsg2_lam"),
    (21, .la .x11 "blsg2_den"),
    (24, .jal .x1 "blsf_copy_quads"),
    (25, .la .x10 "blsg2_lam"),
    (27, .la .x11 "blsg2_den"),
    (29, .jal .x1 "blsg2_fp2_add"),
    (30, .la .x10 "blsg2_lam"),
    (32, .la .x11 "blsg2_den"),
    (34, .jal .x1 "blsg2_fp2_add"),
    (36, .la .x11 "blsg2_den"),
    (39, .jal .x1 "blsf_copy_quads"),
    (40, .la .x10 "blsg2_den"),
    (43, .jal .x1 "blsg2_fp2_add"),
    (44, .la .x10 "blsg2_den"),
    (46, .la .x11 "blsg2_inv_out"),
    (48, .jal .x1 "blsg2_fp2_inv"),
    (49, .la .x10 "blsg2_lam"),
    (51, .la .x11 "blsg2_inv_out"),
    (53, .jal .x1 "blsg2_fp2_mul"),
    (57, .jal .x1 "blsg2_chord_tail"),
    (61, .jal .x1 "blsg2_zero192") ]

def bls12G2PointDblFunction : String :=
  "blsg2_point_dbl:\n" ++ emitProgramR blsg2PointDbl_prog blsg2PointDbl_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2PointDbl_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2PointDblFunction_eq_prog :
    bls12G2PointDblFunction = "blsg2_point_dbl:\n" ++ emitProgramR blsg2PointDbl_prog blsg2PointDbl_relocs := rfl

#guard bls12G2PointDblFunction.startsWith "blsg2_point_dbl:\n"
#guard blsg2PointDbl_prog.length = 68
/-- Add two affine LE points: a0 = P, a1 = Q, a2 = out (192 B LE; out
    may alias). Software-handles infinity, equal-x doubling, and
    P + (-P). Returns a0 = 1 when the result is infinity. -/
def blsg2PointAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .LI .x11 (192 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_point_add + 40)),
    .BEQ .x10 .x0 (32 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_copy192 (GuestAddrs.blsg2_point_add + 56)),
    .MV .x10 .x18,
    .LI .x11 (192 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_point_add + 68)),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_point_add + 316) (GuestAddrs.blsg2_point_add + 72)),
    .MV .x10 .x9,
    .LI .x11 (192 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_point_add + 84)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_copy192 (GuestAddrs.blsg2_point_add + 100)),
    .LI .x10 (0 : Word),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_point_add + 316) (GuestAddrs.blsg2_point_add + 108)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg2_eq_n (GuestAddrs.blsg2_point_add + 124)),
    .BEQ .x10 .x0 (40 : BitVec 13),
    .ADDI .x10 .x8 (96 : BitVec 12),
    .ADDI .x11 .x9 (96 : BitVec 12),
    .LI .x12 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg2_eq_n (GuestAddrs.blsg2_point_add + 144)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg2_point_add + 304) (GuestAddrs.blsg2_point_add + 148)),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_point_dbl (GuestAddrs.blsg2_point_add + 160)),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_point_add + 316) (GuestAddrs.blsg2_point_add + 164)),
    .ADDI .x10 .x9 (96 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 172)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 172)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_point_add + 184)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 188)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 188)),
    .ADDI .x11 .x8 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_point_add + 200)),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 208)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 208)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_point_add + 220)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 224)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 224)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_sub (GuestAddrs.blsg2_point_add + 236)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 240)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_den (GuestAddrs.blsg2_point_add + 240)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_add + 248)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_add + 248)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_inv (GuestAddrs.blsg2_point_add + 256)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 260)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_lam (GuestAddrs.blsg2_point_add + 260)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_add + 268)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_inv_out (GuestAddrs.blsg2_point_add + 268)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_point_add + 276)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_chord_tail (GuestAddrs.blsg2_point_add + 292)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_zero192 (GuestAddrs.blsg2_point_add + 308)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2PointAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2PointAdd_relocs : RelocTable :=
  [ (10, .jal .x1 "blsg_is_zero_n"),
    (14, .jal .x1 "blsg2_copy192"),
    (17, .jal .x1 "blsg_is_zero_n"),
    (21, .jal .x1 "blsg_is_zero_n"),
    (25, .jal .x1 "blsg2_copy192"),
    (31, .jal .x1 "blsg2_eq_n"),
    (36, .jal .x1 "blsg2_eq_n"),
    (40, .jal .x1 "blsg2_point_dbl"),
    (43, .la .x11 "blsg2_lam"),
    (46, .jal .x1 "blsf_copy_quads"),
    (47, .la .x10 "blsg2_lam"),
    (50, .jal .x1 "blsg2_fp2_sub"),
    (52, .la .x11 "blsg2_den"),
    (55, .jal .x1 "blsf_copy_quads"),
    (56, .la .x10 "blsg2_den"),
    (59, .jal .x1 "blsg2_fp2_sub"),
    (60, .la .x10 "blsg2_den"),
    (62, .la .x11 "blsg2_inv_out"),
    (64, .jal .x1 "blsg2_fp2_inv"),
    (65, .la .x10 "blsg2_lam"),
    (67, .la .x11 "blsg2_inv_out"),
    (69, .jal .x1 "blsg2_fp2_mul"),
    (73, .jal .x1 "blsg2_chord_tail"),
    (77, .jal .x1 "blsg2_zero192") ]

def bls12G2PointAddFunction : String :=
  "blsg2_point_add:\n" ++ emitProgramR blsg2PointAdd_prog blsg2PointAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2PointAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2PointAddFunction_eq_prog :
    bls12G2PointAddFunction = "blsg2_point_add:\n" ++ emitProgramR blsg2PointAdd_prog blsg2PointAdd_relocs := rfl

#guard bls12G2PointAddFunction.startsWith "blsg2_point_add:\n"
#guard blsg2PointAdd_prog.length = 85
/-- Decode one EIP-2537 G2 wire point (a0 = 256-byte padded BE record,
    byte reads) into a 192-byte LE point at a1: each of the four 64-byte
    field elements needs a zero 16-byte pad and a 48-byte value < p, and
    the point must be all-zero (infinity) or satisfy y^2 = x^3 + 4(u+1).
    Returns a0 = 0 (valid finite), 1 (infinity), or 2 (invalid). -/
def blsg2DecodeG2_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x18 (0 : Word),
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .LI .x11 (16 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_decode_g2 + 44)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg2_decode_g2 + 284) (GuestAddrs.blsg2_decode_g2 + 48)),
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .ADDI .x10 .x10 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg_lt_p (GuestAddrs.blsg2_decode_g2 + 64)),
    .BEQ .x10 .x0 (brOff (GuestAddrs.blsg2_decode_g2 + 284) (GuestAddrs.blsg2_decode_g2 + 68)),
    .SLLI .x5 .x18 (6 : BitVec 6),
    .ADD .x10 .x8 .x5,
    .ADDI .x10 .x10 (16 : BitVec 12),
    .SLLI .x5 .x18 (4 : BitVec 6),
    .SLLI .x6 .x18 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x11 .x9 .x5,
    .JAL .x1 (jalOff GuestAddrs.blsg_be_to_le (GuestAddrs.blsg2_decode_g2 + 100)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x18 .x5 (brOff (GuestAddrs.blsg2_decode_g2 + 32) (GuestAddrs.blsg2_decode_g2 + 112)),
    .MV .x10 .x9,
    .LI .x11 (192 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_decode_g2 + 124)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_decode_g2 + 288) (GuestAddrs.blsg2_decode_g2 + 136)),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 144)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 144)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_decode_g2 + 156)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 160)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 160)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_decode_g2 + 172)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 176)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 176)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_decode_g2 + 188)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 192)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 192)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_b_le (GuestAddrs.blsg2_decode_g2 + 200)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_b_le (GuestAddrs.blsg2_decode_g2 + 200)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_add (GuestAddrs.blsg2_decode_g2 + 208)),
    .ADDI .x10 .x9 (96 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 216)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 216)),
    .LI .x12 (12 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsf_copy_quads (GuestAddrs.blsg2_decode_g2 + 228)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 232)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 232)),
    .ADDI .x11 .x9 (96 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.blsg2_fp2_mul (GuestAddrs.blsg2_decode_g2 + 244)),
    .AUIPC .x10 (laHi GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 248)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg2_oc_t (GuestAddrs.blsg2_decode_g2 + 248)),
    .AUIPC .x11 (laHi GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 256)),
    .ADDI .x11 .x11 (laLo GuestAddrs.blsg2_oc_y2 (GuestAddrs.blsg2_decode_g2 + 256)),
    .LI .x12 (96 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg2_eq_n (GuestAddrs.blsg2_decode_g2 + 268)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2DecodeG2_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2DecodeG2_relocs : RelocTable :=
  [ (11, .jal .x1 "blsg_is_zero_n"),
    (16, .jal .x1 "blsg_lt_p"),
    (25, .jal .x1 "blsg_be_to_le"),
    (31, .jal .x1 "blsg_is_zero_n"),
    (36, .la .x11 "blsg2_oc_t"),
    (39, .jal .x1 "blsf_copy_quads"),
    (40, .la .x10 "blsg2_oc_t"),
    (43, .jal .x1 "blsg2_fp2_mul"),
    (44, .la .x10 "blsg2_oc_t"),
    (47, .jal .x1 "blsg2_fp2_mul"),
    (48, .la .x10 "blsg2_oc_t"),
    (50, .la .x11 "blsg2_b_le"),
    (52, .jal .x1 "blsg2_fp2_add"),
    (54, .la .x11 "blsg2_oc_y2"),
    (57, .jal .x1 "blsf_copy_quads"),
    (58, .la .x10 "blsg2_oc_y2"),
    (61, .jal .x1 "blsg2_fp2_mul"),
    (62, .la .x10 "blsg2_oc_t"),
    (64, .la .x11 "blsg2_oc_y2"),
    (67, .jal .x1 "blsg2_eq_n") ]

def bls12G2DecodeFunction : String :=
  "blsg2_decode_g2:\n" ++ emitProgramR blsg2DecodeG2_prog blsg2DecodeG2_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2DecodeG2_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2DecodeFunction_eq_prog :
    bls12G2DecodeFunction = "blsg2_decode_g2:\n" ++ emitProgramR blsg2DecodeG2_prog blsg2DecodeG2_relocs := rfl

#guard bls12G2DecodeFunction.startsWith "blsg2_decode_g2:\n"
#guard blsg2DecodeG2_prog.length = 78
/-- Multiply an affine LE point by a big-endian scalar (MSB-first
    double-and-add over the raw bytes). a0 = scalar bytes, a1 = scalar
    byte length, a2 = base point, a3 = output (192 B LE; must not alias
    the base). Returns a0 = 1 when the result is infinity. -/
def blsg2ScalarMul_prog : Program :=
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
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_zero192 (GuestAddrs.blsg2_scalar_mul + 60)),
    .LI .x19 (1 : Word),
    .LI .x20 (0 : Word),
    .BGEU .x20 .x23 (brOff (GuestAddrs.blsg2_scalar_mul + 192) (GuestAddrs.blsg2_scalar_mul + 72)),
    .ADD .x5 .x8 .x20,
    .LBU .x21 .x5 (0 : BitVec 12),
    .LI .x22 (128 : Word),
    .BEQ .x22 .x0 (brOff (GuestAddrs.blsg2_scalar_mul + 184) (GuestAddrs.blsg2_scalar_mul + 88)),
    .BNE .x19 .x0 (20 : BitVec 13),
    .MV .x10 .x18,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_point_dbl (GuestAddrs.blsg2_scalar_mul + 104)),
    .MV .x19 .x10,
    .AND .x5 .x21 .x22,
    .BEQ .x5 .x0 (60 : BitVec 13),
    .BEQ .x19 .x0 (36 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_copy192 (GuestAddrs.blsg2_scalar_mul + 132)),
    .MV .x10 .x18,
    .LI .x11 (192 : Word),
    .JAL .x1 (jalOff GuestAddrs.blsg_is_zero_n (GuestAddrs.blsg2_scalar_mul + 144)),
    .MV .x19 .x10,
    .JAL .x0 (24 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.blsg2_point_add (GuestAddrs.blsg2_scalar_mul + 168)),
    .MV .x19 .x10,
    .SRLI .x22 .x22 (1 : BitVec 6),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_scalar_mul + 88) (GuestAddrs.blsg2_scalar_mul + 180)),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (jalOff (GuestAddrs.blsg2_scalar_mul + 72) (GuestAddrs.blsg2_scalar_mul + 188)),
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
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2ScalarMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2ScalarMul_relocs : RelocTable :=
  [ (15, .jal .x1 "blsg2_zero192"),
    (26, .jal .x1 "blsg2_point_dbl"),
    (33, .jal .x1 "blsg2_copy192"),
    (36, .jal .x1 "blsg_is_zero_n"),
    (42, .jal .x1 "blsg2_point_add") ]

def bls12G2ScalarMulFunction : String :=
  "blsg2_scalar_mul:\n" ++ emitProgramR blsg2ScalarMul_prog blsg2ScalarMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2ScalarMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2ScalarMulFunction_eq_prog :
    bls12G2ScalarMulFunction = "blsg2_scalar_mul:\n" ++ emitProgramR blsg2ScalarMul_prog blsg2ScalarMul_relocs := rfl

#guard bls12G2ScalarMulFunction.startsWith "blsg2_scalar_mul:\n"
#guard blsg2ScalarMul_prog.length = 60
/-- EIP-2537 G2 subgroup check: a0 = LE point. a0 = 1 iff n*P = inf. -/
def blsg2SubgroupG2_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .MV .x12 .x10,
    .AUIPC .x10 (laHi GuestAddrs.blsg_n_be (GuestAddrs.blsg2_subgroup_g2 + 12)),
    .ADDI .x10 .x10 (laLo GuestAddrs.blsg_n_be (GuestAddrs.blsg2_subgroup_g2 + 12)),
    .LI .x11 (32 : Word),
    .AUIPC .x13 (laHi GuestAddrs.blsg2_sub_out (GuestAddrs.blsg2_subgroup_g2 + 24)),
    .ADDI .x13 .x13 (laLo GuestAddrs.blsg2_sub_out (GuestAddrs.blsg2_subgroup_g2 + 24)),
    .JAL .x1 (jalOff GuestAddrs.blsg2_scalar_mul (GuestAddrs.blsg2_subgroup_g2 + 32)),
    .LD .x1 .x2 (0 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2SubgroupG2_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2SubgroupG2_relocs : RelocTable :=
  [ (3, .la .x10 "blsg_n_be"),
    (6, .la .x13 "blsg2_sub_out"),
    (8, .jal .x1 "blsg2_scalar_mul") ]

def bls12G2SubgroupFunction : String :=
  "blsg2_subgroup_g2:\n" ++ emitProgramR blsg2SubgroupG2_prog blsg2SubgroupG2_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2SubgroupG2_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2SubgroupFunction_eq_prog :
    bls12G2SubgroupFunction = "blsg2_subgroup_g2:\n" ++ emitProgramR blsg2SubgroupG2_prog blsg2SubgroupG2_relocs := rfl

#guard bls12G2SubgroupFunction.startsWith "blsg2_subgroup_g2:\n"
#guard blsg2SubgroupG2_prog.length = 12
/-- Encode an LE point as the compact 192-byte BE record (4 × 48-byte
    BE felts) at a1; all-zero stays all-zero. -/
def blsg2Encode_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LI .x18 (0 : Word),
    .SLLI .x5 .x18 (4 : BitVec 6),
    .SLLI .x6 .x18 (5 : BitVec 6),
    .ADD .x5 .x5 .x6,
    .ADD .x10 .x8 .x5,
    .ADD .x11 .x9 .x5,
    .JAL .x1 (jalOff GuestAddrs.blsg_le_to_be (GuestAddrs.blsg2_encode + 52)),
    .ADDI .x18 .x18 (1 : BitVec 12),
    .LI .x5 (4 : Word),
    .BNE .x18 .x5 (-32 : BitVec 13),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `blsg2Encode_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def blsg2Encode_relocs : RelocTable :=
  [ (13, .jal .x1 "blsg_le_to_be") ]

def bls12G2EncodeFunction : String :=
  "blsg2_encode:\n" ++ emitProgramR blsg2Encode_prog blsg2Encode_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `blsg2Encode_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bls12G2EncodeFunction_eq_prog :
    bls12G2EncodeFunction = "blsg2_encode:\n" ++ emitProgramR blsg2Encode_prog blsg2Encode_relocs := rfl

#guard bls12G2EncodeFunction.startsWith "blsg2_encode:\n"
#guard blsg2Encode_prog.length = 23
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
