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
#guard bncCopy64_prog.length = 9
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
#guard bncZero64_prog.length = 7
/-- Return a0 = 1 iff the 64-byte point at a0 is (0,0) (infinity). -/
def bncIsInf64_prog : Program :=
  [ .LI .x5 (64 : Word),
    .MV .x6 .x10,
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

def bn254PointIsInfFunction : String :=
  "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bncIsInf64_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254PointIsInfFunction_eq_prog :
    bn254PointIsInfFunction = "bnc_is_inf64:\n" ++ emitProgram bncIsInf64_prog := rfl

#guard bn254PointIsInfFunction.startsWith "bnc_is_inf64:\n"
#guard bncIsInf64_prog.length = 12
/-- Double an affine point. a0 = input x||y (BE), a1 = output x||y.
    Returns a0 = 1 when the result is infinity (y = 0 input, which also
    covers the (0,0) infinity encoding), output zeroed; else 0. -/
def bn254PointDblFunction : String :=
  "bnc_point_dbl:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  addi a0, s0, 32\n" ++
  "  jal ra, bnf_is_zero32\n" ++
  "  beqz a0, .Lbnc_dbl_finite\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, bnc_zero64\n" ++
  "  li a0, 1\n" ++
  "  j .Lbnc_dbl_ret\n" ++
  ".Lbnc_dbl_finite:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, bnc_le_p1\n" ++
  "  jal ra, bnf_be_to_le          # p1.x\n" ++
  "  addi a0, s0, 32\n" ++
  "  la a1, bnc_le_p1\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, bnf_be_to_le          # p1.y\n" ++
  "  la t0, bnc_le_p1\n" ++
  "  .4byte 0x8072a073             # csrs 0x807, t0 -> Bn254CurveDbl\n" ++
  "  la a0, bnc_le_p1\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnf_le_to_be          # out.x\n" ++
  "  la a0, bnc_le_p1\n" ++
  "  addi a0, a0, 32\n" ++
  "  addi a1, s1, 32\n" ++
  "  jal ra, bnf_le_to_be          # out.y\n" ++
  "  li a0, 0\n" ++
  ".Lbnc_dbl_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two affine points. a0 = P, a1 = Q, a2 = out (all 64-byte BE x||y,
    infinity = (0,0)). Handles the accelerator-excluded cases in software:
    P or Q at infinity, equal x with equal y (doubling), and equal x with
    opposite y (result infinity). Returns a0 = 1 when the result is
    infinity (output zeroed), else 0. -/
def bn254PointAddFunction : String :=
  "bnc_point_add:\n" ++
  "  addi sp, sp, -40\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  mv s0, a0; mv s1, a1; mv s2, a2\n" ++
  "  mv a0, s0\n" ++
  "  jal ra, bnc_is_inf64\n" ++
  "  beqz a0, .Lbnc_add_p_finite\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_copy64            # P = inf: result = Q\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, bnc_is_inf64\n" ++
  "  j .Lbnc_add_ret\n" ++
  ".Lbnc_add_p_finite:\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, bnc_is_inf64\n" ++
  "  beqz a0, .Lbnc_add_q_finite\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_copy64            # Q = inf: result = P (finite)\n" ++
  "  li a0, 0\n" ++
  "  j .Lbnc_add_ret\n" ++
  ".Lbnc_add_q_finite:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnf_eq32\n" ++
  "  beqz a0, .Lbnc_add_distinct_x\n" ++
  "  addi a0, s0, 32\n" ++
  "  addi a1, s1, 32\n" ++
  "  jal ra, bnf_eq32\n" ++
  "  beqz a0, .Lbnc_add_inf        # x equal, y opposite: P + (-P) = inf\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_point_dbl         # x and y equal: P + P\n" ++
  "  j .Lbnc_add_ret\n" ++
  ".Lbnc_add_distinct_x:\n" ++
  "  mv a0, s0\n" ++
  "  la a1, bnc_le_p1\n" ++
  "  jal ra, bnf_be_to_le          # p1.x\n" ++
  "  addi a0, s0, 32\n" ++
  "  la a1, bnc_le_p1\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, bnf_be_to_le          # p1.y\n" ++
  "  mv a0, s1\n" ++
  "  la a1, bnc_le_p2\n" ++
  "  jal ra, bnf_be_to_le          # p2.x\n" ++
  "  addi a0, s1, 32\n" ++
  "  la a1, bnc_le_p2\n" ++
  "  addi a1, a1, 32\n" ++
  "  jal ra, bnf_be_to_le          # p2.y\n" ++
  "  la t0, bnc_add_params\n" ++
  "  .4byte 0x8062a073             # csrs 0x806, t0 -> Bn254CurveAdd\n" ++
  "  la a0, bnc_le_p1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnf_le_to_be          # out.x\n" ++
  "  la a0, bnc_le_p1\n" ++
  "  addi a0, a0, 32\n" ++
  "  addi a1, s2, 32\n" ++
  "  jal ra, bnf_le_to_be          # out.y\n" ++
  "  li a0, 0\n" ++
  "  j .Lbnc_add_ret\n" ++
  ".Lbnc_add_inf:\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, bnc_zero64\n" ++
  "  li a0, 1\n" ++
  ".Lbnc_add_ret:\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  addi sp, sp, 40\n" ++
  "  ret"

/-- a0 = 1 iff the finite point at a0 (coords already `< p`) satisfies
    y^2 = x^3 + 3 mod p. -/
def bn254OnCurveFunction : String :=
  "bnc_on_curve:\n" ++
  "  addi sp, sp, -16\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv a1, s0\n" ++
  "  la a2, bnc_t\n" ++
  "  jal ra, bnf_mul_mod_p         # t = x^2\n" ++
  "  la a0, bnc_t\n" ++
  "  mv a1, s0\n" ++
  "  la a2, bnc_t\n" ++
  "  jal ra, bnf_mul_mod_p         # t = x^3\n" ++
  "  la a0, bnc_t\n" ++
  "  la a1, bnf_b_be\n" ++
  "  la a2, bnc_rhs\n" ++
  "  jal ra, bnf_add_mod_p         # rhs = x^3 + 3\n" ++
  "  addi a0, s0, 32\n" ++
  "  addi a1, s0, 32\n" ++
  "  la a2, bnc_y2\n" ++
  "  jal ra, bnf_mul_mod_p         # y2 = y^2\n" ++
  "  la a0, bnc_rhs\n" ++
  "  la a1, bnc_y2\n" ++
  "  jal ra, bnf_eq32\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp)\n" ++
  "  addi sp, sp, 16\n" ++
  "  ret"

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
#guard bncValidateG1_prog.length = 24
/-- Multiply an affine point by a 256-bit big-endian scalar (MSB-first
    double-and-add; the scalar is NOT reduced mod the group order, matching
    execution-specs `multiply(p0, n)` over the raw 32-byte value — the G1
    cofactor is 1, so this agrees with reduction mod the order).
    a0 = scalar (32-byte BE), a1 = base x||y, a2 = output x||y. Returns
    a0 = 1 when the result is infinity (output zeroed). -/
def bn254ScalarMulFunction : String :=
  "bnc_scalar_mul:\n" ++
  "  addi sp, sp, -72\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp)\n" ++
  "  mv s0, a0                      # scalar bytes\n" ++
  "  mv s1, a1                      # base point\n" ++
  "  mv s2, a2                      # accumulator/output\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, bnc_zero64\n" ++
  "  li s3, 1                       # accumulator is infinity\n" ++
  "  li s4, 0                       # byte index\n" ++
  ".Lbnc_mul_byte_loop:\n" ++
  "  li t0, 32\n" ++
  "  bgeu s4, t0, .Lbnc_mul_done\n" ++
  "  add t0, s0, s4\n" ++
  "  lbu s5, 0(t0)\n" ++
  "  li s6, 128\n" ++
  ".Lbnc_mul_bit_loop:\n" ++
  "  beqz s6, .Lbnc_mul_next_byte\n" ++
  "  bnez s3, .Lbnc_mul_skip_double\n" ++
  "  mv a0, s2\n" ++
  "  la a1, bnc_point_tmp\n" ++
  "  jal ra, bnc_point_dbl\n" ++
  "  mv s3, a0\n" ++
  "  la a0, bnc_point_tmp\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_copy64\n" ++
  ".Lbnc_mul_skip_double:\n" ++
  "  and t0, s5, s6\n" ++
  "  beqz t0, .Lbnc_mul_advance_bit\n" ++
  "  beqz s3, .Lbnc_mul_add_base\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_copy64\n" ++
  "  mv a0, s2\n" ++
  "  jal ra, bnc_is_inf64\n" ++
  "  mv s3, a0                      # base may itself be (0,0)\n" ++
  "  j .Lbnc_mul_advance_bit\n" ++
  ".Lbnc_mul_add_base:\n" ++
  "  mv a0, s2\n" ++
  "  mv a1, s1\n" ++
  "  la a2, bnc_point_tmp\n" ++
  "  jal ra, bnc_point_add\n" ++
  "  mv s3, a0\n" ++
  "  la a0, bnc_point_tmp\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, bnc_copy64\n" ++
  ".Lbnc_mul_advance_bit:\n" ++
  "  srli s6, s6, 1\n" ++
  "  j .Lbnc_mul_bit_loop\n" ++
  ".Lbnc_mul_next_byte:\n" ++
  "  addi s4, s4, 1\n" ++
  "  j .Lbnc_mul_byte_loop\n" ++
  ".Lbnc_mul_done:\n" ++
  "  mv a0, s3\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp)\n" ++
  "  addi sp, sp, 72\n" ++
  "  ret"

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
#guard bn254CallAllotment_prog.length = 13
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

def ziskBn254G1AddRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBn254G1AddRealProbePrologue
  dataAsm     := bn254CurveDataSection
}

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

def ziskBn254G1MulRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskBn254G1MulRealProbePrologue
  dataAsm     := bn254CurveDataSection
}

end EvmAsm.Codegen
