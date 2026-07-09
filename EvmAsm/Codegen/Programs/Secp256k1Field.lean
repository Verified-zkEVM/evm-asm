/-
  EvmAsm.Codegen.Programs.Secp256k1Field

  Codegen-only secp256k1 prime-field helpers for staged software
  public-key recovery. Values are 32-byte big-endian integers.

  The modular multiplies (`secf_mul_mod_p`, `secf_mul_mod_n`) are backed by
  the ziskemu `Arith256Mod` accelerator (`csrs 0x802` with a parameter-block
  pointer, emitted as a pre-encoded `.4byte` so the plain `rv64imac`
  toolchain assembles it). Inputs convert between the 32-byte big-endian
  call surface and the accelerator's little-endian u64-limb format via
  `secf_be_to_le` / `secf_le_to_be`.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Secp256k1FieldIsZeroSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- secp256k1 field prime, p = 2^256 - 0x1000003d1, as a data section fragment. -/
def secp256k1FieldDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "secp256k1_p_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xfe,0xff,0xff,0xfc,0x2f\n" ++
  "secp256k1_c_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x01,0x00,0x00,0x03,0xd1\n" ++
  "secp256k1_one_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01\n" ++
  "secp256k1_p_minus_2_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xfe,0xff,0xff,0xfc,0x2d\n" ++
  -- sqrt exponent (p+1)/4 for the Tonelli-Shanks-free square root (p ≡ 3 mod 4).
  -- Kept as a documented reference for the hardcoded skip-bit ladder in
  -- `secfSqrtModP_prog` (its zero bits are {255,254,30,7,6,5,4,1,0}; bit 0 is
  -- handled by that routine's separate `BEQ x19,x0` rather than the LI/BEQ
  -- chain, which lists {255,254,30,7,6,5,4,1}). The routine does NOT read this
  -- datum — it exists only to pin the intended exponent. The previous bytes
  -- (…fb,ff,ff,ff,0c) did NOT equal (p+1)/4 (wrong at bits 30 and 34); corrected
  -- below to the true value (…ff,bf,ff,ff,0c). Verified: value == (p+1)/4.
  "secp256k1_sqrt_exp_be:\n" ++
  "  .byte 0x3f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xbf,0xff,0xff,0x0c\n" ++
  -- secp256k1 group order n, its 2^256 complement (2^256 - n, for folding an
  -- add carry back like `secp256k1_c_be` does for p), and n-2 (the Fermat
  -- exponent for the scalar inverse). Used by the mod-n scalar helpers.
  "secf_n_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "secf_n_c_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x01\n" ++
  "  .byte 0x45,0x51,0x23,0x19,0x50,0xb7,0x5f,0xc4\n" ++
  "  .byte 0x40,0x2d,0xa1,0x73,0x2f,0xc9,0xbe,0xbf\n" ++
  "secf_n_minus_2_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x3f\n" ++
  ".balign 8\n" ++
  "secf_tmp0:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "secf_cmp:\n" ++
  "  .zero 8\n" ++
  -- Little-endian 4x-u64-limb staging for the ziskemu `Arith256Mod`
  -- accelerator (`d = (a*b + c) mod module`), plus its two static parameter
  -- blocks (one per modulus). The accelerator reads {a,b,c,module} and writes
  -- d; `secf_le_zero` doubles as the read-only c = 0.
  ".balign 8\n" ++
  "secf_le_a:\n" ++
  "  .zero 32\n" ++
  "secf_le_b:\n" ++
  "  .zero 32\n" ++
  "secf_le_d:\n" ++
  "  .zero 32\n" ++
  "secf_le_zero:\n" ++
  "  .zero 32\n" ++
  "secf_le_p:\n" ++
  "  .quad 0xFFFFFFFEFFFFFC2F, 0xFFFFFFFFFFFFFFFF\n" ++
  "  .quad 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF\n" ++
  "secf_le_n:\n" ++
  "  .quad 0xBFD25E8CD0364141, 0xBAAEDCE6AF48A03B\n" ++
  "  .quad 0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF\n" ++
  "secf_arith_params_p:\n" ++
  "  .quad secf_le_a, secf_le_b, secf_le_zero, secf_le_p, secf_le_d\n" ++
  "secf_arith_params_n:\n" ++
  "  .quad secf_le_a, secf_le_b, secf_le_zero, secf_le_n, secf_le_d\n" ++
  ".balign 8\n" ++
  "secf_pow_result:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "secf_pow_base:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "secf_pow_verify:\n" ++
  "  .zero 32\n"

/-- Copy 32 bytes from `a0` to `a1`. Leaf helper. -/
def secfCopy32_prog : Program :=
  [ .LD .x5 .x10 (0 : BitVec 12),
    .SD .x11 .x5 (0 : BitVec 12),
    .LD .x5 .x10 (8 : BitVec 12),
    .SD .x11 .x5 (8 : BitVec 12),
    .LD .x5 .x10 (16 : BitVec 12),
    .SD .x11 .x5 (16 : BitVec 12),
    .LD .x5 .x10 (24 : BitVec 12),
    .SD .x11 .x5 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def secp256k1FieldCopy32Function : String :=
  "secf_copy32:\n" ++ emitProgram secfCopy32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfCopy32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldCopy32Function_eq_prog :
    secp256k1FieldCopy32Function = "secf_copy32:\n" ++ emitProgram secfCopy32_prog := rfl

#guard secp256k1FieldCopy32Function.startsWith "secf_copy32:\n"
#guard secfCopy32_prog.length = 9
/-- Zero a 32-byte buffer. Leaf helper. -/
def secfZero32_prog : Program :=
  [ .SD .x10 .x0 (0 : BitVec 12),
    .SD .x10 .x0 (8 : BitVec 12),
    .SD .x10 .x0 (16 : BitVec 12),
    .SD .x10 .x0 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def secp256k1FieldZero32Function : String :=
  "secf_zero32:\n" ++ emitProgram secfZero32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfZero32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldZero32Function_eq_prog :
    secp256k1FieldZero32Function = "secf_zero32:\n" ++ emitProgram secfZero32_prog := rfl

#guard secp256k1FieldZero32Function.startsWith "secf_zero32:\n"
#guard secfZero32_prog.length = 5
/-- Convert a 32-byte big-endian buffer (`a0`, byte-addressed, any alignment)
    into four little-endian u64 limbs (`a1`, 8-aligned), least-significant
    limb first — the ziskemu accelerator operand format. Leaf helper;
    clobbers only `t` registers. -/
def secfBeToLe_prog : Program :=
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

def secp256k1FieldBeToLeFunction : String :=
  "secf_be_to_le:\n" ++ emitProgram secfBeToLe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfBeToLe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldBeToLeFunction_eq_prog :
    secp256k1FieldBeToLeFunction = "secf_be_to_le:\n" ++ emitProgram secfBeToLe_prog := rfl

#guard secp256k1FieldBeToLeFunction.startsWith "secf_be_to_le:\n"
#guard secfBeToLe_prog.length = 20
/-- Convert four little-endian u64 limbs (`a0`, 8-aligned) into a 32-byte
    big-endian buffer (`a1`, byte-addressed, any alignment). Inverse of
    `secf_be_to_le`. Leaf helper; clobbers only `t` registers. -/
def secfLeToBe_prog : Program :=
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

def secp256k1FieldLeToBeFunction : String :=
  "secf_le_to_be:\n" ++ emitProgram secfLeToBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfLeToBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldLeToBeFunction_eq_prog :
    secp256k1FieldLeToBeFunction = "secf_le_to_be:\n" ++ emitProgram secfLeToBe_prog := rfl

#guard secp256k1FieldLeToBeFunction.startsWith "secf_le_to_be:\n"
#guard secfLeToBe_prog.length = 19
/-- Return bit `a1` of a 32-byte BE field element, numbering bits from the LSB. -/
def secfGetBitLsb_prog : Program :=
  [ .SRLI .x5 .x11 (3 : BitVec 6),
    .LI .x6 (31 : Word),
    .SUB .x5 .x6 .x5,
    .ADD .x5 .x10 .x5,
    .LBU .x6 .x5 (0 : BitVec 12),
    .ANDI .x7 .x11 (7 : BitVec 12),
    .SRL .x6 .x6 .x7,
    .ANDI .x10 .x6 (1 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def secp256k1FieldGetBitFunction : String :=
  "secf_get_bit_lsb:\n" ++ emitProgram secfGetBitLsb_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfGetBitLsb_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldGetBitFunction_eq_prog :
    secp256k1FieldGetBitFunction = "secf_get_bit_lsb:\n" ++ emitProgram secfGetBitLsb_prog := rfl

#guard secp256k1FieldGetBitFunction.startsWith "secf_get_bit_lsb:\n"
#guard secfGetBitLsb_prog.length = 9
/-- Return a0 = 1 iff the 32-byte BE buffer at a0 is zero. Leaf helper.

    Re-emitted drop-in: the verified `Secp256k1FieldIsZeroSAsm.secfIsZero32Body`
    flatten + `ret` (12 instructions, same length as the pre-drop-in two-exit scan). -/
def secfIsZero32_prog : Program :=
  Secp256k1FieldIsZeroSAsm.secfIsZero32_prog

def secp256k1FieldIsZeroFunction : String :=
  "secf_is_zero32:\n" ++ emitProgram secfIsZero32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    the verified re-emitted `secfIsZero32_prog` rendered under its label. -/
theorem secp256k1FieldIsZeroFunction_eq_prog :
    secp256k1FieldIsZeroFunction = "secf_is_zero32:\n" ++ emitProgram secfIsZero32_prog := rfl

#guard secp256k1FieldIsZeroFunction.startsWith "secf_is_zero32:\n"
#guard secfIsZero32_prog.length = 12
/-- Return a0 = 1 iff the two 32-byte BE buffers at a0 and a1 are equal. Leaf helper. -/
def secfEq32_prog : Program :=
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

def secp256k1FieldEq32Function : String :=
  "secf_eq32:\n" ++ emitProgram secfEq32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `secfEq32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem secp256k1FieldEq32Function_eq_prog :
    secp256k1FieldEq32Function = "secf_eq32:\n" ++ emitProgram secfEq32_prog := rfl

#guard secp256k1FieldEq32Function.startsWith "secf_eq32:\n"
#guard secfEq32_prog.length = 15
/--
  Compare a 32-byte big-endian integer against the secp256k1 field prime.

  Calling convention:
    a0: input pointer
    a1: u64 output pointer; stores 0 for `< p`, 1 for `== p`, 2 for `> p`
    returns a0 = 0.
-/
def secfCmpP_prog : Program :=
  [ .AUIPC .x5 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_cmp_p + 0)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_cmp_p + 0)),
    .LI .x6 (32 : Word),
    .MV .x7 .x10,
    .BEQ .x6 .x0 (48 : BitVec 13),
    .LBU .x28 .x7 (0 : BitVec 12),
    .LBU .x29 .x5 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (48 : BitVec 13),
    .ADDI .x7 .x7 (1 : BitVec 12),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .SD .x11 .x0 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x11 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x5 (2 : Word),
    .SD .x11 .x5 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfCmpP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfCmpP_relocs : RelocTable :=
  [ (0, .la .x5 "secp256k1_p_be") ]

def secp256k1FieldCmpPFunction : String :=
  "secf_cmp_p:\n" ++ emitProgramR secfCmpP_prog secfCmpP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfCmpP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldCmpPFunction_eq_prog :
    secp256k1FieldCmpPFunction = "secf_cmp_p:\n" ++ emitProgramR secfCmpP_prog secfCmpP_relocs := rfl

#guard secp256k1FieldCmpPFunction.startsWith "secf_cmp_p:\n"
#guard secfCmpP_prog.length = 24
/--
  Reduce a value known to be below `2p` by subtracting p at most once.

  Calling convention:
    a0: input pointer
    a1: output pointer
    returns a0 = 1 if p was subtracted, else 0.
-/
def secfReduceOnce_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 28)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 28)),
    .AUIPC .x12 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 36)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 36)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.secf_reduce_once + 44)),
    .AUIPC .x5 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (32 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 68)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secf_reduce_once + 68)),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_reduce_once + 80)),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_reduce_once + 100)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfReduceOnce_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfReduceOnce_relocs : RelocTable :=
  [ (7, .la .x11 "secp256k1_p_be"),
    (9, .la .x12 "secf_cmp"),
    (11, .jal .x1 "u256_lt_be"),
    (12, .la .x5 "secf_cmp"),
    (17, .la .x11 "secp256k1_p_be"),
    (20, .jal .x1 "u256_sub_be"),
    (25, .jal .x1 "secf_copy32") ]

def secp256k1FieldReduceOnceFunction : String :=
  "secf_reduce_once:\n" ++ emitProgramR secfReduceOnce_prog secfReduceOnce_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfReduceOnce_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldReduceOnceFunction_eq_prog :
    secp256k1FieldReduceOnceFunction = "secf_reduce_once:\n" ++ emitProgramR secfReduceOnce_prog secfReduceOnce_relocs := rfl

#guard secp256k1FieldReduceOnceFunction.startsWith "secf_reduce_once:\n"
#guard secfReduceOnce_prog.length = 32
/-- Add two field elements modulo p. Inputs and output are 32-byte BE buffers. -/
def secfAddModP_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_p + 40)),
    .ADDI .x19 .x19 (laLo GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_p + 40)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 60)),
    .MV .x20 .x10,
    .BEQ .x20 .x0 (24 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_c_be (GuestAddrs.secf_add_mod_p + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_c_be (GuestAddrs.secf_add_mod_p + 76)),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_p + 88)),
    .MV .x10 .x19,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once (GuestAddrs.secf_add_mod_p + 100)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfAddModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfAddModP_relocs : RelocTable :=
  [ (10, .la .x19 "secf_tmp0"),
    (15, .jal .x1 "u256_add_be"),
    (19, .la .x11 "secp256k1_c_be"),
    (22, .jal .x1 "u256_add_be"),
    (25, .jal .x1 "secf_reduce_once") ]

def secp256k1FieldAddFunction : String :=
  "secf_add_mod_p:\n" ++ emitProgramR secfAddModP_prog secfAddModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfAddModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldAddFunction_eq_prog :
    secp256k1FieldAddFunction = "secf_add_mod_p:\n" ++ emitProgramR secfAddModP_prog secfAddModP_relocs := rfl

#guard secp256k1FieldAddFunction.startsWith "secf_add_mod_p:\n"
#guard secfAddModP_prog.length = 35
/-- Subtract two field elements modulo p. Inputs and output are 32-byte BE buffers. -/
def secfSubModP_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi GuestAddrs.secf_tmp0 (GuestAddrs.secf_sub_mod_p + 40)),
    .ADDI .x19 .x19 (laLo GuestAddrs.secf_tmp0 (GuestAddrs.secf_sub_mod_p + 40)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 60)),
    .MV .x20 .x10,
    .BEQ .x20 .x0 (28 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_c_be (GuestAddrs.secf_sub_mod_p + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_c_be (GuestAddrs.secf_sub_mod_p + 76)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_sub_mod_p + 88)),
    .JAL .x0 (16 : BitVec 21),
    .MV .x10 .x19,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_sub_mod_p + 104)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfSubModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfSubModP_relocs : RelocTable :=
  [ (10, .la .x19 "secf_tmp0"),
    (15, .jal .x1 "u256_sub_be"),
    (19, .la .x11 "secp256k1_c_be"),
    (22, .jal .x1 "u256_sub_be"),
    (26, .jal .x1 "secf_copy32") ]

def secp256k1FieldSubFunction : String :=
  "secf_sub_mod_p:\n" ++ emitProgramR secfSubModP_prog secfSubModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfSubModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldSubFunction_eq_prog :
    secp256k1FieldSubFunction = "secf_sub_mod_p:\n" ++ emitProgramR secfSubModP_prog secfSubModP_relocs := rfl

#guard secp256k1FieldSubFunction.startsWith "secf_sub_mod_p:\n"
#guard secfSubModP_prog.length = 36
/--
  Multiply two field elements modulo p via the ziskemu `Arith256Mod`
  accelerator: `d = (a*b + 0) mod p` with exact 512-bit intermediate math,
  so unreduced 256-bit inputs are accepted and the output is fully reduced.
  The raw `.4byte 0x8022a073` is `csrs 0x802, t0` (`SYSCALL_ARITH256_MOD_ID`
  with the parameter-block pointer in `t0`), pre-encoded so the
  `-march=rv64imac` toolchain assembles it without `Zicsr` (the same pattern
  as the Keccak-f probe's `.4byte 0x80052073`).
-/
def secfMulModP_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.secf_le_a (GuestAddrs.secf_mul_mod_p + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_le_a (GuestAddrs.secf_mul_mod_p + 24)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_p + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secf_le_b (GuestAddrs.secf_mul_mod_p + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_le_b (GuestAddrs.secf_mul_mod_p + 40)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_p + 48)),
    .AUIPC .x5 (laHi GuestAddrs.secf_arith_params_p (GuestAddrs.secf_mul_mod_p + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_arith_params_p (GuestAddrs.secf_mul_mod_p + 52)),
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.secf_le_d (GuestAddrs.secf_mul_mod_p + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_le_d (GuestAddrs.secf_mul_mod_p + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secf_mul_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfMulModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfMulModP_relocs : RelocTable :=
  [ (6, .la .x11 "secf_le_a"),
    (8, .jal .x1 "secf_be_to_le"),
    (10, .la .x11 "secf_le_b"),
    (12, .jal .x1 "secf_be_to_le"),
    (13, .la .x5 "secf_arith_params_p"),
    (16, .la .x10 "secf_le_d"),
    (19, .jal .x1 "secf_le_to_be") ]

def secp256k1FieldMulFunction : String :=
  "secf_mul_mod_p:\n" ++ emitProgramR secfMulModP_prog secfMulModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfMulModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldMulFunction_eq_prog :
    secp256k1FieldMulFunction = "secf_mul_mod_p:\n" ++ emitProgramR secfMulModP_prog secfMulModP_relocs := rfl

#guard secp256k1FieldMulFunction.startsWith "secf_mul_mod_p:\n"
#guard secfMulModP_prog.length = 26
/-- Square one field element modulo p. -/
def secfSquareModP_prog : Program :=
  [ .MV .x11 .x10,
    .JAL .x0 (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secf_square_mod_p + 4)) ]

/-- Reloc side-table for `secfSquareModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfSquareModP_relocs : RelocTable :=
  [ (1, .jal .x0 "secf_mul_mod_p") ]

def secp256k1FieldSquareFunction : String :=
  "secf_square_mod_p:\n" ++ emitProgramR secfSquareModP_prog secfSquareModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfSquareModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldSquareFunction_eq_prog :
    secp256k1FieldSquareFunction = "secf_square_mod_p:\n" ++ emitProgramR secfSquareModP_prog secfSquareModP_relocs := rfl

#guard secp256k1FieldSquareFunction.startsWith "secf_square_mod_p:\n"
#guard secfSquareModP_prog.length = 2
/-- Modular exponentiation by a 256-bit BE exponent using square-and-multiply. -/
def secfPowModP_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x20 (laHi GuestAddrs.secf_pow_result (GuestAddrs.secf_pow_mod_p + 44)),
    .ADDI .x20 .x20 (laLo GuestAddrs.secf_pow_result (GuestAddrs.secf_pow_mod_p + 44)),
    .AUIPC .x21 (laHi GuestAddrs.secf_pow_base (GuestAddrs.secf_pow_mod_p + 52)),
    .ADDI .x21 .x21 (laLo GuestAddrs.secf_pow_base (GuestAddrs.secf_pow_mod_p + 52)),
    .AUIPC .x10 (laHi GuestAddrs.secp256k1_one_be (GuestAddrs.secf_pow_mod_p + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secp256k1_one_be (GuestAddrs.secf_pow_mod_p + 60)),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_pow_mod_p + 72)),
    .MV .x10 .x8,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once (GuestAddrs.secf_pow_mod_p + 84)),
    .LI .x19 (255 : Word),
    .MV .x10 .x20,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_square_mod_p (GuestAddrs.secf_pow_mod_p + 100)),
    .MV .x10 .x9,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.secf_get_bit_lsb (GuestAddrs.secf_pow_mod_p + 112)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secf_pow_mod_p + 132)),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .MV .x10 .x20,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_pow_mod_p + 156)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfPowModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfPowModP_relocs : RelocTable :=
  [ (11, .la .x20 "secf_pow_result"),
    (13, .la .x21 "secf_pow_base"),
    (15, .la .x10 "secp256k1_one_be"),
    (18, .jal .x1 "secf_copy32"),
    (21, .jal .x1 "secf_reduce_once"),
    (25, .jal .x1 "secf_square_mod_p"),
    (28, .jal .x1 "secf_get_bit_lsb"),
    (33, .jal .x1 "secf_mul_mod_p"),
    (39, .jal .x1 "secf_copy32") ]

def secp256k1FieldPowFunction : String :=
  "secf_pow_mod_p:\n" ++ emitProgramR secfPowModP_prog secfPowModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfPowModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldPowFunction_eq_prog :
    secp256k1FieldPowFunction = "secf_pow_mod_p:\n" ++ emitProgramR secfPowModP_prog secfPowModP_relocs := rfl

#guard secp256k1FieldPowFunction.startsWith "secf_pow_mod_p:\n"
#guard secfPowModP_prog.length = 50
/-- Invert a nonzero field element. Returns a0 = 1 for zero input, else 0. -/
def secfInvModP_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secf_inv_mod_p + 24)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secf_inv_mod_p + 36)),
    .LI .x10 (1 : Word),
    .JAL .x0 (40 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.secp256k1_p_minus_2_be (GuestAddrs.secf_inv_mod_p + 48)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secp256k1_p_minus_2_be (GuestAddrs.secf_inv_mod_p + 48)),
    .ADDI .x11 .x2 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_inv_mod_p + 60)),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (24 : BitVec 12),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_pow_mod_p (GuestAddrs.secf_inv_mod_p + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfInvModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfInvModP_relocs : RelocTable :=
  [ (6, .jal .x1 "secf_is_zero32"),
    (9, .jal .x1 "secf_zero32"),
    (12, .la .x10 "secp256k1_p_minus_2_be"),
    (15, .jal .x1 "secf_copy32"),
    (19, .jal .x1 "secf_pow_mod_p") ]

def secp256k1FieldInvFunction : String :=
  "secf_inv_mod_p:\n" ++ emitProgramR secfInvModP_prog secfInvModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfInvModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldInvFunction_eq_prog :
    secp256k1FieldInvFunction = "secf_inv_mod_p:\n" ++ emitProgramR secfInvModP_prog secfInvModP_relocs := rfl

#guard secp256k1FieldInvFunction.startsWith "secf_inv_mod_p:\n"
#guard secfInvModP_prog.length = 26
/-- Square root modulo p. Returns a0 = 1 if no root exists, else 0.

    Square-and-multiply for x^((p+1)/4) (p ≡ 3 mod 4). The multiply is SKIPPED
    at each bit where the exponent (p+1)/4 is zero. The zero bits of (p+1)/4 are
    {255,254,30,7,6,5,4,1,0}: bits {255,254,30,7,6,5,4,1} are matched by the
    `LI x5,k; BEQ x19,x5` chain below, and bit 0 by the separate `BEQ x19,x0`.
    These bits must equal the zero bits of `secp256k1_sqrt_exp_be` = (p+1)/4;
    keep the two in sync if either changes. -/
def secfSqrtModP_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .SD .x2 .x20 (32 : BitVec 12),
    .SD .x2 .x21 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .AUIPC .x20 (laHi GuestAddrs.secf_pow_result (GuestAddrs.secf_sqrt_mod_p + 36)),
    .ADDI .x20 .x20 (laLo GuestAddrs.secf_pow_result (GuestAddrs.secf_sqrt_mod_p + 36)),
    .AUIPC .x21 (laHi GuestAddrs.secf_pow_base (GuestAddrs.secf_sqrt_mod_p + 44)),
    .ADDI .x21 .x21 (laLo GuestAddrs.secf_pow_base (GuestAddrs.secf_sqrt_mod_p + 44)),
    .AUIPC .x10 (laHi GuestAddrs.secp256k1_one_be (GuestAddrs.secf_sqrt_mod_p + 52)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secp256k1_one_be (GuestAddrs.secf_sqrt_mod_p + 52)),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_sqrt_mod_p + 64)),
    .MV .x10 .x8,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once (GuestAddrs.secf_sqrt_mod_p + 76)),
    .LI .x19 (255 : Word),
    .MV .x10 .x20,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_square_mod_p (GuestAddrs.secf_sqrt_mod_p + 92)),
    .LI .x5 (255 : Word),
    .BEQ .x19 .x5 (84 : BitVec 13),
    .LI .x5 (254 : Word),
    .BEQ .x19 .x5 (76 : BitVec 13),
    .LI .x5 (30 : Word),
    .BEQ .x19 .x5 (68 : BitVec 13),
    .LI .x5 (7 : Word),
    .BEQ .x19 .x5 (60 : BitVec 13),
    .LI .x5 (6 : Word),
    .BEQ .x19 .x5 (52 : BitVec 13),
    .LI .x5 (5 : Word),
    .BEQ .x19 .x5 (44 : BitVec 13),
    .LI .x5 (4 : Word),
    .BEQ .x19 .x5 (36 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x19 .x5 (28 : BitVec 13),
    .BEQ .x19 .x0 (20 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secf_sqrt_mod_p + 176)),
    .BEQ .x19 .x0 (16 : BitVec 13),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (-108 : BitVec 21),
    .MV .x10 .x20,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_sqrt_mod_p + 204)),
    .MV .x10 .x9,
    .AUIPC .x12 (laHi GuestAddrs.secf_pow_verify (GuestAddrs.secf_sqrt_mod_p + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_pow_verify (GuestAddrs.secf_sqrt_mod_p + 212)),
    .JAL .x1 (jalOff GuestAddrs.secf_square_mod_p (GuestAddrs.secf_sqrt_mod_p + 220)),
    .AUIPC .x10 (laHi GuestAddrs.secf_pow_verify (GuestAddrs.secf_sqrt_mod_p + 224)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_pow_verify (GuestAddrs.secf_sqrt_mod_p + 224)),
    .MV .x11 .x8,
    .JAL .x1 (jalOff GuestAddrs.secf_eq32 (GuestAddrs.secf_sqrt_mod_p + 236)),
    .BNE .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secf_sqrt_mod_p + 248)),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .LD .x20 .x2 (32 : BitVec 12),
    .LD .x21 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfSqrtModP_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfSqrtModP_relocs : RelocTable :=
  [ (9, .la .x20 "secf_pow_result"),
    (11, .la .x21 "secf_pow_base"),
    (13, .la .x10 "secp256k1_one_be"),
    (16, .jal .x1 "secf_copy32"),
    (19, .jal .x1 "secf_reduce_once"),
    (23, .jal .x1 "secf_square_mod_p"),
    (44, .jal .x1 "secf_mul_mod_p"),
    (51, .jal .x1 "secf_copy32"),
    (53, .la .x12 "secf_pow_verify"),
    (55, .jal .x1 "secf_square_mod_p"),
    (56, .la .x10 "secf_pow_verify"),
    (59, .jal .x1 "secf_eq32"),
    (62, .jal .x1 "secf_zero32") ]

def secp256k1FieldSqrtFunction : String :=
  "secf_sqrt_mod_p:\n" ++ emitProgramR secfSqrtModP_prog secfSqrtModP_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfSqrtModP_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1FieldSqrtFunction_eq_prog :
    secp256k1FieldSqrtFunction = "secf_sqrt_mod_p:\n" ++ emitProgramR secfSqrtModP_prog secfSqrtModP_relocs := rfl

#guard secp256k1FieldSqrtFunction.startsWith "secf_sqrt_mod_p:\n"
#guard secfSqrtModP_prog.length = 74
/-! ## Scalar field (mod the group order n)

  ECDSA public-key recovery needs the scalar inverse `r^{-1} mod n`, where `n`
  is the secp256k1 group order rather than the field prime `p`. The helpers
  below mirror the mod-p stack one-for-one, swapping only the modulus constant
  (`secf_n_be` / `secf_n_c_be`) and the Fermat exponent (`secf_n_minus_2_be`).
  The multiply is the same modulus-parameterized `Arith256Mod` accelerator
  call, so no special reduction is required. Scratch buffers (`secf_le_a`,
  `secf_le_b`, `secf_le_d`, `secf_pow_result`, `secf_pow_base`, `secf_tmp0`,
  `secf_cmp`) are reused from the mod-p helpers: the two stacks never run
  concurrently. -/

/-- Reduce a value known to be below `2n` by subtracting n at most once.
    a0 = input, a1 = output; returns a0 = 1 if n was subtracted, else 0. -/
def secfReduceOnceN_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secf_n_be (GuestAddrs.secf_reduce_once_n + 28)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_n_be (GuestAddrs.secf_reduce_once_n + 28)),
    .AUIPC .x12 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once_n + 36)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once_n + 36)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.secf_reduce_once_n + 44)),
    .AUIPC .x5 (laHi GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once_n + 48)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_cmp (GuestAddrs.secf_reduce_once_n + 48)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (32 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secf_n_be (GuestAddrs.secf_reduce_once_n + 68)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_n_be (GuestAddrs.secf_reduce_once_n + 68)),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secf_reduce_once_n + 80)),
    .LI .x10 (1 : Word),
    .JAL .x0 (20 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_reduce_once_n + 100)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfReduceOnceN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfReduceOnceN_relocs : RelocTable :=
  [ (7, .la .x11 "secf_n_be"),
    (9, .la .x12 "secf_cmp"),
    (11, .jal .x1 "u256_lt_be"),
    (12, .la .x5 "secf_cmp"),
    (17, .la .x11 "secf_n_be"),
    (20, .jal .x1 "u256_sub_be"),
    (25, .jal .x1 "secf_copy32") ]

def secp256k1ScalarFieldReduceOnceFunction : String :=
  "secf_reduce_once_n:\n" ++ emitProgramR secfReduceOnceN_prog secfReduceOnceN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfReduceOnceN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldReduceOnceFunction_eq_prog :
    secp256k1ScalarFieldReduceOnceFunction = "secf_reduce_once_n:\n" ++ emitProgramR secfReduceOnceN_prog secfReduceOnceN_relocs := rfl

#guard secp256k1ScalarFieldReduceOnceFunction.startsWith "secf_reduce_once_n:\n"
#guard secfReduceOnceN_prog.length = 32
/-- Add two scalars modulo n. Inputs and output are 32-byte BE buffers. -/
def secfAddModN_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x19 (laHi GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_n + 40)),
    .ADDI .x19 .x19 (laLo GuestAddrs.secf_tmp0 (GuestAddrs.secf_add_mod_n + 40)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_n + 60)),
    .MV .x20 .x10,
    .BEQ .x20 .x0 (24 : BitVec 13),
    .MV .x10 .x19,
    .AUIPC .x11 (laHi GuestAddrs.secf_n_c_be (GuestAddrs.secf_add_mod_n + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_n_c_be (GuestAddrs.secf_add_mod_n + 76)),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secf_add_mod_n + 88)),
    .MV .x10 .x19,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once_n (GuestAddrs.secf_add_mod_n + 100)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfAddModN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfAddModN_relocs : RelocTable :=
  [ (10, .la .x19 "secf_tmp0"),
    (15, .jal .x1 "u256_add_be"),
    (19, .la .x11 "secf_n_c_be"),
    (22, .jal .x1 "u256_add_be"),
    (25, .jal .x1 "secf_reduce_once_n") ]

def secp256k1ScalarFieldAddFunction : String :=
  "secf_add_mod_n:\n" ++ emitProgramR secfAddModN_prog secfAddModN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfAddModN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldAddFunction_eq_prog :
    secp256k1ScalarFieldAddFunction = "secf_add_mod_n:\n" ++ emitProgramR secfAddModN_prog secfAddModN_relocs := rfl

#guard secp256k1ScalarFieldAddFunction.startsWith "secf_add_mod_n:\n"
#guard secfAddModN_prog.length = 35
/-- Multiply two scalars modulo n via the ziskemu `Arith256Mod` accelerator
    (same route as `secf_mul_mod_p`, with the modulus parameter block
    pointing at n instead of p). -/
def secfMulModN_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .AUIPC .x11 (laHi GuestAddrs.secf_le_a (GuestAddrs.secf_mul_mod_n + 24)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_le_a (GuestAddrs.secf_mul_mod_n + 24)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_n + 32)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secf_le_b (GuestAddrs.secf_mul_mod_n + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secf_le_b (GuestAddrs.secf_mul_mod_n + 40)),
    .JAL .x1 (jalOff GuestAddrs.secf_be_to_le (GuestAddrs.secf_mul_mod_n + 48)),
    .AUIPC .x5 (laHi GuestAddrs.secf_arith_params_n (GuestAddrs.secf_mul_mod_n + 52)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_arith_params_n (GuestAddrs.secf_mul_mod_n + 52)),
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.secf_le_d (GuestAddrs.secf_mul_mod_n + 64)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_le_d (GuestAddrs.secf_mul_mod_n + 64)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_le_to_be (GuestAddrs.secf_mul_mod_n + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfMulModN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfMulModN_relocs : RelocTable :=
  [ (6, .la .x11 "secf_le_a"),
    (8, .jal .x1 "secf_be_to_le"),
    (10, .la .x11 "secf_le_b"),
    (12, .jal .x1 "secf_be_to_le"),
    (13, .la .x5 "secf_arith_params_n"),
    (16, .la .x10 "secf_le_d"),
    (19, .jal .x1 "secf_le_to_be") ]

def secp256k1ScalarFieldMulFunction : String :=
  "secf_mul_mod_n:\n" ++ emitProgramR secfMulModN_prog secfMulModN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfMulModN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldMulFunction_eq_prog :
    secp256k1ScalarFieldMulFunction = "secf_mul_mod_n:\n" ++ emitProgramR secfMulModN_prog secfMulModN_relocs := rfl

#guard secp256k1ScalarFieldMulFunction.startsWith "secf_mul_mod_n:\n"
#guard secfMulModN_prog.length = 26
/-- Square one scalar modulo n. -/
def secfSquareModN_prog : Program :=
  [ .MV .x11 .x10,
    .JAL .x0 (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secf_square_mod_n + 4)) ]

/-- Reloc side-table for `secfSquareModN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfSquareModN_relocs : RelocTable :=
  [ (1, .jal .x0 "secf_mul_mod_n") ]

def secp256k1ScalarFieldSquareFunction : String :=
  "secf_square_mod_n:\n" ++ emitProgramR secfSquareModN_prog secfSquareModN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfSquareModN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldSquareFunction_eq_prog :
    secp256k1ScalarFieldSquareFunction = "secf_square_mod_n:\n" ++ emitProgramR secfSquareModN_prog secfSquareModN_relocs := rfl

#guard secp256k1ScalarFieldSquareFunction.startsWith "secf_square_mod_n:\n"
#guard secfSquareModN_prog.length = 2
/-- Modular exponentiation modulo n by a 256-bit BE exponent. -/
def secfPowModN_prog : Program :=
  [ .ADDI .x2 .x2 (-80 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x20 (laHi GuestAddrs.secf_pow_result (GuestAddrs.secf_pow_mod_n + 44)),
    .ADDI .x20 .x20 (laLo GuestAddrs.secf_pow_result (GuestAddrs.secf_pow_mod_n + 44)),
    .AUIPC .x21 (laHi GuestAddrs.secf_pow_base (GuestAddrs.secf_pow_mod_n + 52)),
    .ADDI .x21 .x21 (laLo GuestAddrs.secf_pow_base (GuestAddrs.secf_pow_mod_n + 52)),
    .AUIPC .x10 (laHi GuestAddrs.secp256k1_one_be (GuestAddrs.secf_pow_mod_n + 60)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secp256k1_one_be (GuestAddrs.secf_pow_mod_n + 60)),
    .MV .x11 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_pow_mod_n + 72)),
    .MV .x10 .x8,
    .MV .x11 .x21,
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once_n (GuestAddrs.secf_pow_mod_n + 84)),
    .LI .x19 (255 : Word),
    .MV .x10 .x20,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_square_mod_n (GuestAddrs.secf_pow_mod_n + 100)),
    .MV .x10 .x9,
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.secf_get_bit_lsb (GuestAddrs.secf_pow_mod_n + 112)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x20,
    .MV .x11 .x21,
    .MV .x12 .x20,
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secf_pow_mod_n + 132)),
    .BEQ .x19 .x0 (12 : BitVec 13),
    .ADDI .x19 .x19 (-1 : BitVec 12),
    .JAL .x0 (-52 : BitVec 21),
    .MV .x10 .x20,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_pow_mod_n + 156)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfPowModN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfPowModN_relocs : RelocTable :=
  [ (11, .la .x20 "secf_pow_result"),
    (13, .la .x21 "secf_pow_base"),
    (15, .la .x10 "secp256k1_one_be"),
    (18, .jal .x1 "secf_copy32"),
    (21, .jal .x1 "secf_reduce_once_n"),
    (25, .jal .x1 "secf_square_mod_n"),
    (28, .jal .x1 "secf_get_bit_lsb"),
    (33, .jal .x1 "secf_mul_mod_n"),
    (39, .jal .x1 "secf_copy32") ]

def secp256k1ScalarFieldPowFunction : String :=
  "secf_pow_mod_n:\n" ++ emitProgramR secfPowModN_prog secfPowModN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfPowModN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldPowFunction_eq_prog :
    secp256k1ScalarFieldPowFunction = "secf_pow_mod_n:\n" ++ emitProgramR secfPowModN_prog secfPowModN_relocs := rfl

#guard secp256k1ScalarFieldPowFunction.startsWith "secf_pow_mod_n:\n"
#guard secfPowModN_prog.length = 50
/-- Invert a nonzero scalar modulo n via Fermat (x^(n-2) mod n).
    Returns a0 = 1 for zero input (output zeroed), else 0. -/
def secfInvModN_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .JAL .x1 (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secf_inv_mod_n + 24)),
    .BEQ .x10 .x0 (20 : BitVec 13),
    .MV .x10 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secf_inv_mod_n + 36)),
    .LI .x10 (1 : Word),
    .JAL .x0 (40 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.secf_n_minus_2_be (GuestAddrs.secf_inv_mod_n + 48)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_n_minus_2_be (GuestAddrs.secf_inv_mod_n + 48)),
    .ADDI .x11 .x2 (24 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secf_inv_mod_n + 60)),
    .MV .x10 .x8,
    .ADDI .x11 .x2 (24 : BitVec 12),
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.secf_pow_mod_n (GuestAddrs.secf_inv_mod_n + 76)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secfInvModN_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secfInvModN_relocs : RelocTable :=
  [ (6, .jal .x1 "secf_is_zero32"),
    (9, .jal .x1 "secf_zero32"),
    (12, .la .x10 "secf_n_minus_2_be"),
    (15, .jal .x1 "secf_copy32"),
    (19, .jal .x1 "secf_pow_mod_n") ]

def secp256k1ScalarFieldInvFunction : String :=
  "secf_inv_mod_n:\n" ++ emitProgramR secfInvModN_prog secfInvModN_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secfInvModN_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1ScalarFieldInvFunction_eq_prog :
    secp256k1ScalarFieldInvFunction = "secf_inv_mod_n:\n" ++ emitProgramR secfInvModN_prog secfInvModN_relocs := rfl

#guard secp256k1ScalarFieldInvFunction.startsWith "secf_inv_mod_n:\n"
#guard secfInvModN_prog.length = 26
/-- Field/scalar suite WITHOUT the generic `u256_add_be`/`u256_sub_be`/
    `u256_lt_be` helpers, for closures that already link them (the
    stateless-guest verdict bundles define their own copies). -/
def secp256k1FieldCommonFunctionsNoU256 : String :=
  secp256k1FieldCopy32Function ++ "\n" ++
  secp256k1FieldZero32Function ++ "\n" ++
  secp256k1FieldBeToLeFunction ++ "\n" ++
  secp256k1FieldLeToBeFunction ++ "\n" ++
  secp256k1FieldGetBitFunction ++ "\n" ++
  secp256k1FieldIsZeroFunction ++ "\n" ++
  secp256k1FieldEq32Function ++ "\n" ++
  secp256k1FieldCmpPFunction ++ "\n" ++
  secp256k1FieldReduceOnceFunction ++ "\n" ++
  secp256k1FieldAddFunction ++ "\n" ++
  secp256k1FieldSubFunction ++ "\n" ++
  secp256k1FieldMulFunction ++ "\n" ++
  secp256k1FieldSquareFunction ++ "\n" ++
  secp256k1FieldPowFunction ++ "\n" ++
  secp256k1FieldInvFunction ++ "\n" ++
  secp256k1FieldSqrtFunction ++ "\n" ++
  secp256k1ScalarFieldReduceOnceFunction ++ "\n" ++
  secp256k1ScalarFieldAddFunction ++ "\n" ++
  secp256k1ScalarFieldMulFunction ++ "\n" ++
  secp256k1ScalarFieldSquareFunction ++ "\n" ++
  secp256k1ScalarFieldPowFunction ++ "\n" ++
  secp256k1ScalarFieldInvFunction

def secp256k1FieldCommonFunctions : String :=
  u256AddBeFunction ++ "\n" ++
  u256SubBeFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  secp256k1FieldCommonFunctionsNoU256

def ziskSecp256k1FieldCmpPPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secf_cmp_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_cmp_probe_done\n" ++
  secp256k1FieldCmpPFunction ++ "\n" ++
  ".Lsecf_cmp_probe_done:"

def ziskSecp256k1FieldReduceOncePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a2, 0x40000000\n" ++
  "  addi a0, a2, 8\n" ++
  "  li a1, 0xa0010010\n" ++
  "  jal ra, secf_reduce_once\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd zero, 0(t0)\n" ++
  "  sd a0, 8(t0)\n" ++
  "  j .Lsecf_reduce_probe_done\n" ++
  u256SubBeFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  secp256k1FieldCopy32Function ++ "\n" ++
  secp256k1FieldReduceOnceFunction ++ "\n" ++
  ".Lsecf_reduce_probe_done:"

def ziskSecp256k1FieldAddPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  addi a1, a3, 40\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, secf_add_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_add_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_add_probe_done:"

def ziskSecp256k1FieldSubPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  addi a1, a3, 40\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, secf_sub_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_sub_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_sub_probe_done:"



def ziskSecp256k1FieldMulPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  addi a1, a3, 40\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_mul_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_mul_probe_done:"


def ziskSecp256k1FieldSquarePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, secf_square_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_square_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_square_probe_done:"


def ziskSecp256k1FieldInvPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secf_inv_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_inv_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_inv_probe_done:"

def ziskSecp256k1FieldSqrtPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secf_sqrt_mod_p\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_sqrt_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_sqrt_probe_done:"

def ziskSecp256k1FieldInvNPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  li a1, 0xa0010008\n" ++
  "  jal ra, secf_inv_mod_n\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecf_invn_probe_done\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecf_invn_probe_done:"


def ziskSecp256k1FieldCmpPProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldCmpPPrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldReduceOnceProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldReduceOncePrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldAddProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldAddPrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldSubProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldSubPrologue
  dataAsm     := secp256k1FieldDataSection
}


def ziskSecp256k1FieldMulProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldMulPrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldSquareProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldSquarePrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldInvProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldInvPrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldSqrtProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldSqrtPrologue
  dataAsm     := secp256k1FieldDataSection
}

def ziskSecp256k1FieldInvNProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1FieldInvNPrologue
  dataAsm     := secp256k1FieldDataSection
}

end EvmAsm.Codegen
