/-
  EvmAsm.Codegen.Programs.Bn254Field

  Codegen-only BN254 (alt_bn128) base-field helpers for the 0x06/0x07/0x08
  EVM precompiles (EIP-196/EIP-197). Values are 32-byte big-endian field
  elements over

    p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
      = 0x30644e72e131a029b85045b68181585d97816a916871ca8d3c208c16d87cfd47

  The modular multiply and add are backed by the ziskemu `Arith256Mod`
  accelerator (`csrs 0x802` with a parameter-block pointer, emitted as a
  pre-encoded `.4byte 0x8022a073` so the plain `rv64imac` toolchain
  assembles it — the same route as `Secp256k1Field`'s `secf_mul_mod_p`):

    * mul: d = (a*b + 0) mod p  (params block `bnf_mul_params`)
    * add: d = (a*1 + b) mod p  (params block `bnf_add_params`)

  Both run with exact 512-bit intermediate math, so unreduced 256-bit
  inputs are accepted and outputs are always fully reduced. Inputs convert
  between the 32-byte big-endian call surface and the accelerator's
  little-endian u64-limb format via `bnf_be_to_le` / `bnf_le_to_be`.

  All helpers are `bnf_`-prefixed so closures can link this chain next to
  the secp256k1 (`secf_`) chain without label clashes, and the chain is
  fully self-contained (no `u256_*` dependencies).
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- BN254 base-field data labels WITHOUT a `.section .data` header, for
    appending to an existing data section (the runtime dispatcher data
    core). `bn254FieldDataSection` adds the header for standalone probes. -/
def bn254FieldDataFragment : String :=
  ".balign 8\n" ++
  "bnf_p_be:\n" ++
  "  .byte 0x30,0x64,0x4e,0x72,0xe1,0x31,0xa0,0x29\n" ++
  "  .byte 0xb8,0x50,0x45,0xb6,0x81,0x81,0x58,0x5d\n" ++
  "  .byte 0x97,0x81,0x6a,0x91,0x68,0x71,0xca,0x8d\n" ++
  "  .byte 0x3c,0x20,0x8c,0x16,0xd8,0x7c,0xfd,0x47\n" ++
  -- Curve constant b = 3 (y^2 = x^3 + 3), as a 32-byte BE field element.
  "bnf_b_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x03\n" ++
  -- Little-endian 4x-u64-limb staging for the ziskemu `Arith256Mod`
  -- accelerator (`d = (a*b + c) mod module`), plus its two static parameter
  -- blocks: mul uses c = 0 (`bnf_le_zero`), add uses b = 1 (`bnf_le_one`)
  -- with the addend in the c slot (`bnf_le_b`).
  ".balign 8\n" ++
  "bnf_le_a:\n" ++
  "  .zero 32\n" ++
  "bnf_le_b:\n" ++
  "  .zero 32\n" ++
  "bnf_le_d:\n" ++
  "  .zero 32\n" ++
  "bnf_le_zero:\n" ++
  "  .zero 32\n" ++
  "bnf_le_one:\n" ++
  "  .quad 1, 0, 0, 0\n" ++
  "bnf_le_p:\n" ++
  "  .quad 0x3C208C16D87CFD47, 0x97816A916871CA8D\n" ++
  "  .quad 0xB85045B68181585D, 0x30644E72E131A029\n" ++
  "bnf_mul_params:\n" ++
  "  .quad bnf_le_a, bnf_le_b, bnf_le_zero, bnf_le_p, bnf_le_d\n" ++
  "bnf_add_params:\n" ++
  "  .quad bnf_le_a, bnf_le_one, bnf_le_b, bnf_le_p, bnf_le_d\n"

/-- Standalone `.data` section for focused probes. -/
def bn254FieldDataSection : String :=
  ".section .data\n" ++ bn254FieldDataFragment

/-- Convert a 32-byte big-endian buffer (`a0`, byte-addressed, any
    alignment) into four little-endian u64 limbs (`a1`, 8-aligned),
    least-significant limb first. Leaf helper; clobbers only `t` regs. -/
def bnfBeToLe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .LI .x6 (24 : Word),
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
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (-68 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254FieldBeToLeFunction : String :=
  "bnf_be_to_le:\n" ++ emitProgram bnfBeToLe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfBeToLe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldBeToLeFunction_eq_prog :
    bn254FieldBeToLeFunction = "bnf_be_to_le:\n" ++ emitProgram bnfBeToLe_prog := rfl

#guard bn254FieldBeToLeFunction.startsWith "bnf_be_to_le:\n"
#guard bnfBeToLe_prog.length = 20
/-- Convert four little-endian u64 limbs (`a0`, 8-aligned) into a 32-byte
    big-endian buffer (`a1`, byte-addressed, any alignment). Inverse of
    `bnf_be_to_le`. Leaf helper; clobbers only `t` regs. -/
def bnfLeToBe_prog : Program :=
  [ .LI .x5 (0 : Word),
    .SLLI .x6 .x5 (3 : BitVec 6),
    .ADD .x7 .x10 .x6,
    .LD .x28 .x7 (0 : BitVec 12),
    .LI .x6 (31 : Word),
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
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (-64 : BitVec 13),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def bn254FieldLeToBeFunction : String :=
  "bnf_le_to_be:\n" ++ emitProgram bnfLeToBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfLeToBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldLeToBeFunction_eq_prog :
    bn254FieldLeToBeFunction = "bnf_le_to_be:\n" ++ emitProgram bnfLeToBe_prog := rfl

#guard bn254FieldLeToBeFunction.startsWith "bnf_le_to_be:\n"
#guard bnfLeToBe_prog.length = 19
/-- Return a0 = 1 iff the 32-byte buffer at a0 is all-zero. Leaf helper. -/
def bnfIsZero32_prog : Program :=
  [ .LI .x5 (32 : Word),
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

def bn254FieldIsZeroFunction : String :=
  "bnf_is_zero32:\n" ++ emitProgram bnfIsZero32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfIsZero32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldIsZeroFunction_eq_prog :
    bn254FieldIsZeroFunction = "bnf_is_zero32:\n" ++ emitProgram bnfIsZero32_prog := rfl

#guard bn254FieldIsZeroFunction.startsWith "bnf_is_zero32:\n"
#guard bnfIsZero32_prog.length = 12
/-- Return a0 = 1 iff the two 32-byte buffers at a0 and a1 are equal. -/
def bnfEq32_prog : Program :=
  [ .LI .x5 (32 : Word),
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

def bn254FieldEq32Function : String :=
  "bnf_eq32:\n" ++ emitProgram bnfEq32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfEq32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldEq32Function_eq_prog :
    bn254FieldEq32Function = "bnf_eq32:\n" ++ emitProgram bnfEq32_prog := rfl

#guard bn254FieldEq32Function.startsWith "bnf_eq32:\n"
#guard bnfEq32_prog.length = 15
/-- Return a0 = 1 iff the 32-byte big-endian integer at a0 is `< p`
    (the EIP-196 coordinate range check). Leaf helper. -/
def bnfLtP_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.bnf_p_be (GuestAddrs.bnf_lt_p + 0)),
    .LI .x6 (32 : Word),
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

def bn254FieldLtPFunction : String :=
  "bnf_lt_p:\n" ++ emitProgram bnfLtP_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `bnfLtP_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem bn254FieldLtPFunction_eq_prog :
    bn254FieldLtPFunction = "bnf_lt_p:\n" ++ emitProgram bnfLtP_prog := rfl

#guard bn254FieldLtPFunction.startsWith "bnf_lt_p:\n"
#guard bnfLtP_prog.length = 17
/-- Multiply two field elements modulo p via the ziskemu `Arith256Mod`
    accelerator: `d = (a*b + 0) mod p`. a0/a1 = 32-byte BE inputs,
    a2 = 32-byte BE output. Always returns a0 = 0. -/
def bn254FieldMulFunction : String :=
  "bnf_mul_mod_p:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, bnf_le_a\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, bnf_le_b\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  la t0, bnf_mul_params\n" ++
  "  .4byte 0x8022a073           # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  la a0, bnf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnf_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two field elements modulo p via the same accelerator with the
    `bnf_add_params` block: `d = (a*1 + b) mod p`. a0/a1 = 32-byte BE
    inputs, a2 = 32-byte BE output. Always returns a0 = 0. -/
def bn254FieldAddFunction : String :=
  "bnf_add_mod_p:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, bnf_le_a\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, bnf_le_b\n" ++
  "  jal ra, bnf_be_to_le\n" ++
  "  la t0, bnf_add_params\n" ++
  "  .4byte 0x8022a073           # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  la a0, bnf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, bnf_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- The full BN254 base-field helper suite (self-contained). -/
def bn254FieldCommonFunctions : String :=
  bn254FieldBeToLeFunction ++ "\n" ++
  bn254FieldLeToBeFunction ++ "\n" ++
  bn254FieldIsZeroFunction ++ "\n" ++
  bn254FieldEq32Function ++ "\n" ++
  bn254FieldLtPFunction ++ "\n" ++
  bn254FieldMulFunction ++ "\n" ++
  bn254FieldAddFunction

end EvmAsm.Codegen
