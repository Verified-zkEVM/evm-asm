/-
  EvmAsm.Codegen.Programs.Bn254Curve

  Codegen-only affine BN254 (alt_bn128) G1 curve helpers plus the runtime
  precompile kernels `zkvm_bn254_g1_add` (0x06 ecAdd) and `zkvm_bn254_g1_mul`
  (0x07 ecMul). Points are 64-byte big-endian affine records x || y; the
  point at infinity is encoded as 64 zero bytes (matching execution-specs
  alt_bn128 `normalize`, which maps the infinity z = 0 to (0, 0)).

  `bnc_point_add` / `bnc_point_dbl` are backed by the ziskemu
  Bn254CurveAdd/Bn254CurveDbl accelerators (`csrs 0x806` / `csrs 0x807`
  with a little-endian-limb parameter pointer, emitted as pre-encoded
  `.4byte`s for the plain `rv64imac` toolchain — the same pattern as
  `Secp256k1Curve`). The affine special cases the accelerators exclude
  (input at infinity, doubling with y = 0, adding points with equal x)
  stay in software.

  `bnc_validate_g1` implements execution-specs `bytes_to_g1` validity:
  both coordinates `< p`, and the point is (0,0) (infinity) or satisfies
  y^2 = x^3 + 3 mod p. Invalid input is a precompile failure (the spec
  raises OutOfGasError), surfaced as a nonzero kernel status.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Bn254Field
import EvmAsm.Codegen.Programs.Bn254CurveIsInfSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- BN254 curve data labels WITHOUT a `.section .data` header (see
    `bn254FieldDataFragment`). `bn254_allot_rest` is the EIP-150 child
    allotment remainder cell used by the dispatcher's bn254 failure path
    (burn-all-forwarded-gas on invalid input). -/
def bn254CurveDataFragment : String :=
  -- Little-endian limb staging for the Bn254CurveAdd/Dbl accelerators
  -- (x||y, four u64 limbs per coordinate, least-significant limb first)
  -- plus the static Bn254CurveAdd parameter block {&p1, &p2}; the result
  -- lands in p1.
  ".balign 8\n" ++
  "bnc_le_p1:\n  .zero 64\n" ++
  "bnc_le_p2:\n  .zero 64\n" ++
  "bnc_add_params:\n  .quad bnc_le_p1, bnc_le_p2\n" ++
  ".balign 8\n" ++
  "bnc_point_tmp:\n  .zero 64\n" ++
  -- on-curve check scratch: t = x^2 / x^3, rhs = x^3 + 3, y2 = y^2
  ".balign 8\n" ++
  "bnc_t:\n  .zero 32\n" ++
  "bnc_rhs:\n  .zero 32\n" ++
  "bnc_y2:\n  .zero 32\n" ++
  ".balign 8\n" ++
  "bn254_allot_rest:\n  .zero 8\n"

/-- Standalone `.data` section (field + curve) for focused probes. -/
def bn254CurveDataSection : String :=
  bn254FieldDataSection ++ bn254CurveDataFragment

/-- Copy 64 bytes from a0 to a1 (byte loop; alignment-free). -/
def bncCopy64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .BEQ .x5 .x0 (28 : BitVec 13),
    .LBU .x6 .x10 (0 : BitVec 12),
    .SB .x11 .x6 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254PointCopy64Function : String :=
  "bnc_copy64:\n" ++ emitProgram bncCopy64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bncCopy64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254PointCopy64Function_eq_prog :
    bn254PointCopy64Function = "bnc_copy64:\n" ++ emitProgram bncCopy64_prog := rfl

#guard bn254PointCopy64Function.startsWith "bnc_copy64:\n"
/-- Zero 64 bytes at a0 (byte loop; alignment-free). -/
def bncZero64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .BEQ .x5 .x0 (20 : BitVec 13),
    .SB .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-16 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254PointZero64Function : String :=
  "bnc_zero64:\n" ++ emitProgram bncZero64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bncZero64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254PointZero64Function_eq_prog :
    bn254PointZero64Function = "bnc_zero64:\n" ++ emitProgram bncZero64_prog := rfl

#guard bn254PointZero64Function.startsWith "bnc_zero64:\n"
/-- Return a0 = 1 iff the 64-byte point at a0 is (0,0) (infinity).
    Re-emitted drop-in: the verified SAsm body has the same instruction count
    as the original two-exit byte scan, but different branch layout. -/
def bncIsInf64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .MV .x6 .x10,
    .BEQ .x5 .x0 (24 : BitVec 13),
    .LBU .x7 .x6 (0 : BitVec 12),
    .BNE .x7 .x0 (16 : BitVec 13),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .JAL .x0 (-20 : BitVec 21),
    .LI .x10 (1 : Word),
    .BEQ .x5 .x0 (8 : BitVec 13),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254PointIsInfFunction : String :=
  "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bncIsInf64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254PointIsInfFunction_eq_prog :
    bn254PointIsInfFunction = "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog := rfl

#guard bn254PointIsInfFunction.startsWith "bnc_is_inf64:\n"

/-- The local generated Program block is the verified SAsm drop-in. -/
theorem bncIsInf64_prog_eq_verified :
    bncIsInf64_prog = Bn254CurveIsInfSAsm.bncIsInf64_prog := rfl

/-- Double an affine point. a0 = input x||y (BE), a1 = output x||y.
    Returns a0 = 1 when the result is infinity (y = 0 input, which also
    covers the (0,0) infinity encoding), output zeroed; else 0. -/
def bncPointDbl_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_is_zero32 (GuestAddrs.bnc_point_dbl + 28)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnc_zero64 (GuestAddrs.bnc_point_dbl + 40)),
    .LI .x10 (1 : Word),
    .JAL .x0 (92 : BitVec 21),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 56)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 56)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_dbl + 64)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 72)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 72)),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_dbl + 84)),
    .AUIPC .x5 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 88)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 88)),
    .CSRS (2055 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 100)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnc_point_dbl + 112)),
    .AUIPC .x10 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_dbl + 116)),
    .ADDI .x10 .x10 (32 : BitVec 12),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnc_point_dbl + 132)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bncPointDbl_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bncPointDbl_relocs : RelocTable :=
  [ (7, .jal .x1 "bnf_is_zero32"),
    (10, .jal .x1 "bnc_zero64"),
    (14, .la .x11 "bnc_le_p1"),
    (16, .jal .x1 "bnf_be_to_le"),
    (18, .la .x11 "bnc_le_p1"),
    (21, .jal .x1 "bnf_be_to_le"),
    (22, .la .x5 "bnc_le_p1"),
    (25, .la .x10 "bnc_le_p1"),
    (28, .jal .x1 "bnf_le_to_be"),
    (29, .la .x10 "bnc_le_p1"),
    (33, .jal .x1 "bnf_le_to_be") ]

def bn254PointDblFunction : String :=
  "bnc_point_dbl:\n" ++ emitProgramR bncPointDbl_prog bncPointDbl_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bncPointDbl_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254PointDblFunction_eq_prog :
    bn254PointDblFunction = "bnc_point_dbl:\n" ++ emitProgramR bncPointDbl_prog bncPointDbl_relocs := rfl

#guard bn254PointDblFunction.startsWith "bnc_point_dbl:\n"
/-- Add two affine points. a0 = P, a1 = Q, a2 = out (all 64-byte BE x||y,
    infinity = (0,0)). Handles the accelerator-excluded cases in software:
    P or Q at infinity, equal x with equal y (doubling), and equal x with
    opposite y (result infinity). Returns a0 = 1 when the result is
    infinity (output zeroed), else 0. -/
def bncPointAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnc_is_inf64 (GuestAddrs.bnc_point_add + 36)),
    .BEQ .x10 .x0 (28 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_copy64 (GuestAddrs.bnc_point_add + 52)),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_is_inf64 (GuestAddrs.bnc_point_add + 60)),
    .JAL .x0 (224 : BitVec 21),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnc_is_inf64 (GuestAddrs.bnc_point_add + 72)),
    .BEQ .x10 .x0 (24 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_copy64 (GuestAddrs.bnc_point_add + 88)),
    .LI .x10 (0 : Word),
    .JAL .x0 (192 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.bnf_eq32 (GuestAddrs.bnc_point_add + 108)),
    .BEQ .x10 .x0 (36 : BitVec 13),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_eq32 (GuestAddrs.bnc_point_add + 124)),
    .BEQ .x10 .x0 (148 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_point_dbl (GuestAddrs.bnc_point_add + 140)),
    .JAL .x0 (144 : BitVec 21),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 152)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 152)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_add + 160)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 168)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 168)),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_add + 180)),
    .MV .x10 .x9,
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p2 (GuestAddrs.bnc_point_add + 188)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p2 (GuestAddrs.bnc_point_add + 188)),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_add + 196)),
    .ADDI .x10 .x9 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.bnc_le_p2 (GuestAddrs.bnc_point_add + 204)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_le_p2 (GuestAddrs.bnc_point_add + 204)),
    .ADDI .x11 .x11 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_be_to_le (GuestAddrs.bnc_point_add + 216)),
    .AUIPC .x5 (laHi GuestAddrs.bnc_add_params (GuestAddrs.bnc_point_add + 220)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnc_add_params (GuestAddrs.bnc_point_add + 220)),
    .CSRS (2054 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 232)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 232)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnc_point_add + 244)),
    .AUIPC .x10 (laHi GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 248)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_le_p1 (GuestAddrs.bnc_point_add + 248)),
    .ADDI .x10 .x10 (32 : BitVec 12),
    .ADDI .x11 .x18 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_le_to_be (GuestAddrs.bnc_point_add + 264)),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_zero64 (GuestAddrs.bnc_point_add + 280)),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bncPointAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bncPointAdd_relocs : RelocTable :=
  [ (9, .jal .x1 "bnc_is_inf64"),
    (13, .jal .x1 "bnc_copy64"),
    (15, .jal .x1 "bnc_is_inf64"),
    (18, .jal .x1 "bnc_is_inf64"),
    (22, .jal .x1 "bnc_copy64"),
    (27, .jal .x1 "bnf_eq32"),
    (31, .jal .x1 "bnf_eq32"),
    (35, .jal .x1 "bnc_point_dbl"),
    (38, .la .x11 "bnc_le_p1"),
    (40, .jal .x1 "bnf_be_to_le"),
    (42, .la .x11 "bnc_le_p1"),
    (45, .jal .x1 "bnf_be_to_le"),
    (47, .la .x11 "bnc_le_p2"),
    (49, .jal .x1 "bnf_be_to_le"),
    (51, .la .x11 "bnc_le_p2"),
    (54, .jal .x1 "bnf_be_to_le"),
    (55, .la .x5 "bnc_add_params"),
    (58, .la .x10 "bnc_le_p1"),
    (61, .jal .x1 "bnf_le_to_be"),
    (62, .la .x10 "bnc_le_p1"),
    (66, .jal .x1 "bnf_le_to_be"),
    (70, .jal .x1 "bnc_zero64") ]

def bn254PointAddFunction : String :=
  "bnc_point_add:\n" ++ emitProgramR bncPointAdd_prog bncPointAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bncPointAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254PointAddFunction_eq_prog :
    bn254PointAddFunction = "bnc_point_add:\n" ++ emitProgramR bncPointAdd_prog bncPointAdd_relocs := rfl

#guard bn254PointAddFunction.startsWith "bnc_point_add:\n"
/-- a0 = 1 iff the finite point at a0 (coords already `< p`) satisfies
    y^2 = x^3 + 3 mod p. -/
def bncOnCurve_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 20)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 20)),
    .JAL .x1 (jalOff GuestAddrs.bnf_mul_mod_p (GuestAddrs.bnc_on_curve + 28)),
    .AUIPC .x10 (laHi GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 32)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 32)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 44)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 44)),
    .JAL .x1 (jalOff GuestAddrs.bnf_mul_mod_p (GuestAddrs.bnc_on_curve + 52)),
    .AUIPC .x10 (laHi GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 56)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_t (GuestAddrs.bnc_on_curve + 56)),
    .AUIPC .x11 (laHi GuestAddrs.bnf_b_be (GuestAddrs.bnc_on_curve + 64)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnf_b_be (GuestAddrs.bnc_on_curve + 64)),
    .AUIPC .x12 (laHi GuestAddrs.bnc_rhs (GuestAddrs.bnc_on_curve + 72)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bnc_rhs (GuestAddrs.bnc_on_curve + 72)),
    .JAL .x1 (jalOff GuestAddrs.bnf_add_mod_p (GuestAddrs.bnc_on_curve + 80)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .ADDI .x11 .x8 (32 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.bnc_y2 (GuestAddrs.bnc_on_curve + 92)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bnc_y2 (GuestAddrs.bnc_on_curve + 92)),
    .JAL .x1 (jalOff GuestAddrs.bnf_mul_mod_p (GuestAddrs.bnc_on_curve + 100)),
    .AUIPC .x10 (laHi GuestAddrs.bnc_rhs (GuestAddrs.bnc_on_curve + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_rhs (GuestAddrs.bnc_on_curve + 104)),
    .AUIPC .x11 (laHi GuestAddrs.bnc_y2 (GuestAddrs.bnc_on_curve + 112)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_y2 (GuestAddrs.bnc_on_curve + 112)),
    .JAL .x1 (jalOff GuestAddrs.bnf_eq32 (GuestAddrs.bnc_on_curve + 120)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bncOnCurve_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bncOnCurve_relocs : RelocTable :=
  [ (5, .la .x12 "bnc_t"),
    (7, .jal .x1 "bnf_mul_mod_p"),
    (8, .la .x10 "bnc_t"),
    (11, .la .x12 "bnc_t"),
    (13, .jal .x1 "bnf_mul_mod_p"),
    (14, .la .x10 "bnc_t"),
    (16, .la .x11 "bnf_b_be"),
    (18, .la .x12 "bnc_rhs"),
    (20, .jal .x1 "bnf_add_mod_p"),
    (23, .la .x12 "bnc_y2"),
    (25, .jal .x1 "bnf_mul_mod_p"),
    (26, .la .x10 "bnc_rhs"),
    (28, .la .x11 "bnc_y2"),
    (30, .jal .x1 "bnf_eq32") ]

def bn254OnCurveFunction : String :=
  "bnc_on_curve:\n" ++ emitProgramR bncOnCurve_prog bncOnCurve_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bncOnCurve_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254OnCurveFunction_eq_prog :
    bn254OnCurveFunction = "bnc_on_curve:\n" ++ emitProgramR bncOnCurve_prog bncOnCurve_relocs := rfl

#guard bn254OnCurveFunction.startsWith "bnc_on_curve:\n"
/-- execution-specs `bytes_to_g1` validity for a staged 64-byte point.
    a0 = point; returns a0 = 0 (valid finite), 1 (the (0,0) infinity
    encoding), or 2 (coordinate >= p, or not on the curve). -/
def bncValidateG1_prog : Program :=
  [ .ADDI .x2 .x2 (-16 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .MV .x8 .x10,
    .JAL .x1 (jalOff GuestAddrs.bnf_lt_p (GuestAddrs.bnc_validate_g1 + 16)),
    .BEQ .x10 .x0 (56 : BitVec 13),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.bnf_lt_p (GuestAddrs.bnc_validate_g1 + 28)),
    .BEQ .x10 .x0 (44 : BitVec 13),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnc_is_inf64 (GuestAddrs.bnc_validate_g1 + 40)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (28 : BitVec 21),
    .MV .x10 .x8,
    .JAL .x1 (jalOff GuestAddrs.bnc_on_curve (GuestAddrs.bnc_validate_g1 + 60)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .ADDI .x2 .x2 (16 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `bncValidateG1_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bncValidateG1_relocs : RelocTable :=
  [ (4, .jal .x1 "bnf_lt_p"),
    (7, .jal .x1 "bnf_lt_p"),
    (10, .jal .x1 "bnc_is_inf64"),
    (15, .jal .x1 "bnc_on_curve") ]

def bn254ValidateG1Function : String :=
  "bnc_validate_g1:\n" ++ emitProgramR bncValidateG1_prog bncValidateG1_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bncValidateG1_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254ValidateG1Function_eq_prog :
    bn254ValidateG1Function = "bnc_validate_g1:\n" ++ emitProgramR bncValidateG1_prog bncValidateG1_relocs := rfl

#guard bn254ValidateG1Function.startsWith "bnc_validate_g1:\n"
/-- Multiply an affine point by a 256-bit big-endian scalar (MSB-first
    double-and-add; the scalar is NOT reduced mod the group order, matching
    execution-specs `multiply(p0, n)` over the raw 32-byte value — the G1
    cofactor is 1, so this agrees with reduction mod the order).
    a0 = scalar (32-byte BE), a1 = base x||y, a2 = output x||y. Returns
    a0 = 1 when the result is infinity (output zeroed). -/
def bncScalarMul_prog : Program :=
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
    .JAL .x1 (jalOff GuestAddrs.bnc_zero64 (GuestAddrs.bnc_scalar_mul + 56)),
    .LI .x19 (1 : Word),
    .LI .x20 (0 : Word),
    .LI .x5 (32 : Word),
    .BGEU .x20 .x5 (156 : BitVec 13),
    .ADD .x5 .x8 .x20,
    .LBU .x21 .x5 (0 : BitVec 12),
    .LI .x22 (128 : Word),
    .BEQ .x22 .x0 (132 : BitVec 13),
    .BNE .x19 .x0 (40 : BitVec 13),
    .MV .x10 .x18,
    .AUIPC .x11 (laHi GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 100)),
    .ADDI .x11 .x11 (laLo GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 100)),
    .JAL .x1 (jalOff GuestAddrs.bnc_point_dbl (GuestAddrs.bnc_scalar_mul + 108)),
    .MV .x19 .x10,
    .AUIPC .x10 (laHi GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 116)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 116)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_copy64 (GuestAddrs.bnc_scalar_mul + 128)),
    .AND .x5 .x21 .x22,
    .BEQ .x5 .x0 (76 : BitVec 13),
    .BEQ .x19 .x0 (32 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_copy64 (GuestAddrs.bnc_scalar_mul + 152)),
    .MV .x10 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_is_inf64 (GuestAddrs.bnc_scalar_mul + 160)),
    .MV .x19 .x10,
    .JAL .x0 (44 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 180)),
    .JAL .x1 (jalOff GuestAddrs.bnc_point_add (GuestAddrs.bnc_scalar_mul + 188)),
    .MV .x19 .x10,
    .AUIPC .x10 (laHi GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 196)),
    .ADDI .x10 .x10 (laLo GuestAddrs.bnc_point_tmp (GuestAddrs.bnc_scalar_mul + 196)),
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.bnc_copy64 (GuestAddrs.bnc_scalar_mul + 208)),
    .SRLI .x22 .x22 (1 : BitVec 6),
    .JAL .x0 (-128 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-156 : BitVec 21),
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

/-- Reloc side-table for `bncScalarMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def bncScalarMul_relocs : RelocTable :=
  [ (14, .jal .x1 "bnc_zero64"),
    (25, .la .x11 "bnc_point_tmp"),
    (27, .jal .x1 "bnc_point_dbl"),
    (29, .la .x10 "bnc_point_tmp"),
    (32, .jal .x1 "bnc_copy64"),
    (38, .jal .x1 "bnc_copy64"),
    (40, .jal .x1 "bnc_is_inf64"),
    (45, .la .x12 "bnc_point_tmp"),
    (47, .jal .x1 "bnc_point_add"),
    (49, .la .x10 "bnc_point_tmp"),
    (52, .jal .x1 "bnc_copy64") ]

def bn254ScalarMulFunction : String :=
  "bnc_scalar_mul:\n" ++ emitProgramR bncScalarMul_prog bncScalarMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `bncScalarMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem bn254ScalarMulFunction_eq_prog :
    bn254ScalarMulFunction = "bnc_scalar_mul:\n" ++ emitProgramR bncScalarMul_prog bncScalarMul_relocs := rfl

#guard bn254ScalarMulFunction.startsWith "bnc_scalar_mul:\n"
/-- Real BN254 ecAdd (0x06) kernel behind the dispatcher's
    `zkvm_bn254_g1_add(p1, p2, result)` ABI: a0/a1 = 64-byte BE x||y
    inputs (zero-padded by the staging copy, per execution-specs
    `buffer_read`), a2 = 64-byte BE output. Returns a0 = 0 on success,
    1 on invalid input (coordinate >= p or point not on curve) — the
    spec's InvalidParameter -> OutOfGasError precompile failure. -/
def zkvmBn254G1AddRealFunction : String :=
  ".globl zkvm_bn254_g1_add\n" ++
  "zkvm_bn254_g1_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  jal ra, bnc_validate_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lbn254_add_invalid\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, bnc_validate_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lbn254_add_invalid\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, bnc_point_add\n" ++
  "  li a0, 0\n" ++
  "  j .Lbn254_add_kret\n" ++
  ".Lbn254_add_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lbn254_add_kret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- Real BN254 ecMul (0x07) kernel behind the dispatcher's
    `zkvm_bn254_g1_mul(point, scalar, result)` ABI: a0 = 64-byte BE point,
    a1 = 32-byte BE scalar (used raw, no order reduction), a2 = 64-byte BE
    output. Returns a0 = 0 on success, 1 on invalid input. -/
def zkvmBn254G1MulRealFunction : String :=
  ".globl zkvm_bn254_g1_mul\n" ++
  "zkvm_bn254_g1_mul:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  jal ra, bnc_validate_g1\n" ++
  "  li t0, 2\n" ++
  "  beq a0, t0, .Lbn254_mul_invalid\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s0\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, bnc_scalar_mul\n" ++
  "  li a0, 0\n" ++
  "  j .Lbn254_mul_kret\n" ++
  ".Lbn254_mul_invalid:\n" ++
  "  li a0, 1\n" ++
  ".Lbn254_mul_kret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- EIP-150 child gas allotment for a precompile call:
    x22 = min(call gas word, remaining - remaining/64), where the gas word
    is the 32-byte stack word at 0(x12) (LE u64 limbs; any value with a
    nonzero high limb caps at the 63/64 send limit) and remaining is the
    dispatcher gas cell at 568(x20). Leaf; clobbers x17/x23/x24, returns
    via x1 (callers inside the precompile dispatch tail use `jal x1`). -/
def bn254CallAllotment_prog : Program :=
  [ .LD .x17 .x20 (568 : BitVec 12),
    .SRLI .x22 .x17 (6 : BitVec 6),
    .SUB .x22 .x17 .x22,
    .LD .x23 .x12 (8 : BitVec 12),
    .LD .x24 .x12 (16 : BitVec 12),
    .OR .x23 .x23 .x24,
    .LD .x24 .x12 (24 : BitVec 12),
    .OR .x23 .x23 .x24,
    .BNE .x23 .x0 (16 : BitVec 13),
    .LD .x23 .x12 (0 : BitVec 12),
    .BGEU .x23 .x22 (8 : BitVec 13),
    .MV .x22 .x23,
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254CallAllotmentFunction : String :=
  "bn254_call_allotment:\n" ++ emitProgram bn254CallAllotment_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bn254CallAllotment_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254CallAllotmentFunction_eq_prog :
    bn254CallAllotmentFunction = "bn254_call_allotment:\n" ++ emitProgram bn254CallAllotment_prog := rfl

#guard bn254CallAllotmentFunction.startsWith "bn254_call_allotment:\n"
/-- The full self-contained BN254 precompile suite (field + curve helpers,
    the two real `zkvm_bn254_g1_*` kernels, and the allotment helper).
    Linked by every closure that embeds the runtime dispatcher; pairs with
    `bn254FieldDataFragment ++ bn254CurveDataFragment` in the data section. -/
def bn254PrecompileFunctions : String :=
  bn254FieldCommonFunctions ++ "\n" ++
  bn254PointCopy64Function ++ "\n" ++
  bn254PointZero64Function ++ "\n" ++
  bn254PointIsInfFunction ++ "\n" ++
  bn254PointDblFunction ++ "\n" ++
  bn254PointAddFunction ++ "\n" ++
  bn254OnCurveFunction ++ "\n" ++
  bn254ValidateG1Function ++ "\n" ++
  bn254ScalarMulFunction ++ "\n" ++
  zkvmBn254G1AddRealFunction ++ "\n" ++
  zkvmBn254G1MulRealFunction ++ "\n" ++
  bn254CallAllotmentFunction

/-- Probe prologue for the real ecAdd kernel: p1 at input+0 (64 B),
    p2 at input+64 (64 B); writes status (u64) at OUTPUT+0 and the
    64-byte result at OUTPUT+8. -/
def ziskBn254G1AddRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s0, 64\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bn254_g1_add\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbn254_add_probe_done\n" ++
  bn254PrecompileFunctions ++ "\n" ++
  ".Lbn254_add_probe_done:"


/-- Probe prologue for the real ecMul kernel: point at input+0 (64 B),
    scalar at input+64 (32 B); writes status (u64) at OUTPUT+0 and the
    64-byte result at OUTPUT+8. -/
def ziskBn254G1MulRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s0, 64\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, zkvm_bn254_g1_mul\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lbn254_mul_probe_done\n" ++
  bn254PrecompileFunctions ++ "\n" ++
  ".Lbn254_mul_probe_done:"


end EvmAsm.Codegen
