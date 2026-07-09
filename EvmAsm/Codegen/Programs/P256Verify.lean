/-
  EvmAsm.Codegen.Programs.P256Verify

  The EIP-7951 P256VERIFY (0x100) kernel `zkvm_secp256r1_verify`,
  mirroring execution-specs `p256verify` + `secp256r1_verify`: full
  ECDSA verification over NIST P-256 (secp256r1).

  There is no P-256 curve accelerator in ziskemu, so the group law is
  software affine chord/tangent (the proven Bls12G2 shape) built from
  single-syscall `Arith256Mod` (csrs 0x802, the secp256k1 recovery
  route) fused ops with the P-256 moduli:

    mul:  d = (a*b + 0) mod m
    add:  d = (a*1 + b) mod p
    sub:  d = (b*(p-1) + a) mod p          (= a - b mod p)
    inv:  Fermat a^(p-2) / s^(n-2) via MSB-first square-and-multiply

  Verification (the gates mirror p256verify.py exactly; ALL failures
  are a successful precompile call with EMPTY returndata, decided by
  the caller from the verified byte — the kernel always returns 0):

    0 < r < n, 0 < s < n, qx < p, qy < p, (qx,qy) != (0,0),
    qy^2 = qx^3 + a*qx + b (mod p), then
    u1 = e*s^-1 mod n, u2 = r*s^-1 mod n, R = u1*G + u2*Q,
    valid iff R != inf and R.x mod n == r.

  P-256 has cofactor 1, so on-curve is the full subgroup check. e is
  the raw 256-bit message hash; the mod-n reduction happens inside the
  u1 multiplication (Arith256Mod takes a full 512-bit intermediate).

  Values are 32-byte big-endian throughout (the secp256k1 staged-
  recovery convention); points are 64-byte x || y with infinity
  tracked in flags (the all-zero encoding never reaches the group
  law). Every input access is a byte access, so the 4-aligned frame
  payload is fine. All labels are `p256_`-prefixed and the suite is
  self-contained (no secf_/blsg_ dependencies — the dispatcher
  branches do not link the secp256k1 chain).

  Kernel ABI (the `.L<tag>_p256verify` entry charges 6900 gas, gates
  length == 160, and stages the payload before the call):

    zkvm_secp256r1_verify(a0 = msg hash (32 B), a1 = sig r||s (64 B),
                          a2 = pubkey qx||qy (64 B),
                          a3 = verified byte ptr)
      -> a0 = 0 always; verified byte = 1 iff the signature checks out.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.P256Eq32SAsm
import EvmAsm.Codegen.Programs.P256IsZeroNSAsm

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- P256VERIFY data labels WITHOUT a `.section .data` header. -/
def p256VerifyDataFragment : String :=
  ".balign 8\n" ++
  -- NIST P-256 domain parameters (32-byte BE)
  "p256_p_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x01\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "p256_n_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xbc,0xe6,0xfa,0xad,0xa7,0x17,0x9e,0x84\n" ++
  "  .byte 0xf3,0xb9,0xca,0xc2,0xfc,0x63,0x25,0x51\n" ++
  "p256_a_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x01\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfc\n" ++
  "p256_b_be:\n" ++
  "  .byte 0x5a,0xc6,0x35,0xd8,0xaa,0x3a,0x93,0xe7\n" ++
  "  .byte 0xb3,0xeb,0xbd,0x55,0x76,0x98,0x86,0xbc\n" ++
  "  .byte 0x65,0x1d,0x06,0xb0,0xcc,0x53,0xb0,0xf6\n" ++
  "  .byte 0x3b,0xce,0x3c,0x3e,0x27,0xd2,0x60,0x4b\n" ++
  "p256_one_be:\n" ++
  "  .zero 31\n" ++
  "  .byte 0x01\n" ++
  -- Fermat exponents p-2 (field inverse) and n-2 (scalar inverse)
  "p256_pm2_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x01\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfd\n" ++
  "p256_nm2_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xbc,0xe6,0xfa,0xad,0xa7,0x17,0x9e,0x84\n" ++
  "  .byte 0xf3,0xb9,0xca,0xc2,0xfc,0x63,0x25,0x4f\n" ++
  -- generator G (64-byte BE x || y)
  "p256_gen_be:\n" ++
  "  .byte 0x6b,0x17,0xd1,0xf2,0xe1,0x2c,0x42,0x47\n" ++
  "  .byte 0xf8,0xbc,0xe6,0xe5,0x63,0xa4,0x40,0xf2\n" ++
  "  .byte 0x77,0x03,0x7d,0x81,0x2d,0xeb,0x33,0xa0\n" ++
  "  .byte 0xf4,0xa1,0x39,0x45,0xd8,0x98,0xc2,0x96\n" ++
  "  .byte 0x4f,0xe3,0x42,0xe2,0xfe,0x1a,0x7f,0x9b\n" ++
  "  .byte 0x8e,0xe7,0xeb,0x4a,0x7c,0x0f,0x9e,0x16\n" ++
  "  .byte 0x2b,0xce,0x33,0x57,0x6b,0x31,0x5e,0xce\n" ++
  "  .byte 0xcb,0xb6,0x40,0x68,0x37,0xbf,0x51,0xf5\n" ++
  -- Arith256Mod staging (LE limbs) + the fused-op parameter blocks
  ".balign 8\n" ++
  "p256_le_a:\n  .zero 32\n" ++
  "p256_le_b:\n  .zero 32\n" ++
  "p256_le_d:\n  .zero 32\n" ++
  "p256_le_zero:\n  .zero 32\n" ++
  "p256_le_one:\n" ++
  "  .quad 1, 0, 0, 0\n" ++
  "p256_le_p:\n" ++
  "  .quad 0xffffffffffffffff, 0x00000000ffffffff\n" ++
  "  .quad 0x0000000000000000, 0xffffffff00000001\n" ++
  "p256_le_n:\n" ++
  "  .quad 0xf3b9cac2fc632551, 0xbce6faada7179e84\n" ++
  "  .quad 0xffffffffffffffff, 0xffffffff00000000\n" ++
  "p256_le_pm1:\n" ++
  "  .quad 0xfffffffffffffffe, 0x00000000ffffffff\n" ++
  "  .quad 0x0000000000000000, 0xffffffff00000001\n" ++
  -- {a, b, c, module, d} blocks: mul/add/sub mod p, mul mod n
  "p256_pb_mul_p:\n" ++
  "  .quad p256_le_a, p256_le_b, p256_le_zero, p256_le_p, p256_le_d\n" ++
  "p256_pb_add_p:\n" ++
  "  .quad p256_le_a, p256_le_one, p256_le_b, p256_le_p, p256_le_d\n" ++
  "p256_pb_sub_p:\n" ++
  "  .quad p256_le_b, p256_le_pm1, p256_le_a, p256_le_p, p256_le_d\n" ++
  "p256_pb_mul_n:\n" ++
  "  .quad p256_le_a, p256_le_b, p256_le_zero, p256_le_n, p256_le_d\n" ++
  -- field scratch (32-byte BE each)
  "p256_lam:\n  .zero 32\n" ++
  "p256_t1:\n  .zero 32\n" ++
  "p256_t2:\n  .zero 32\n" ++
  "p256_den:\n  .zero 32\n" ++
  "p256_inv_out:\n  .zero 32\n" ++
  "p256_acc:\n  .zero 32\n" ++
  "p256_sinv:\n  .zero 32\n" ++
  "p256_u1:\n  .zero 32\n" ++
  "p256_u2:\n  .zero 32\n" ++
  "p256_v:\n  .zero 32\n" ++
  -- affine point working set (64-byte BE x || y each)
  "p256_p1:\n  .zero 64\n" ++
  "p256_p2:\n  .zero 64\n" ++
  "p256_ptmp:\n  .zero 64\n"

/-- Copy a2 bytes from a0 to a1. Leaf. -/
def p256CopyN_prog : Program :=
  [ .BEQ .x12 .x0 (28 : BitVec 13),
    .LBU .x5 .x10 (0 : BitVec 12),
    .SB .x11 .x5 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (1 : BitVec 12),
    .ADDI .x12 .x12 (-1 : BitVec 12),
    .JAL .x0 (-24 : BitVec 21),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def p256CopyNFunction : String :=
  "p256_copy_n:\n" ++ emitProgram p256CopyN_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256CopyN_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256CopyNFunction_eq_prog :
    p256CopyNFunction = "p256_copy_n:\n" ++ emitProgram p256CopyN_prog := rfl

#guard p256CopyNFunction.startsWith "p256_copy_n:\n"
#guard p256CopyN_prog.length = 8
/-- a0 = 1 iff the a1 bytes at a0 are all zero. Leaf. -/
def p256IsZeroN_prog : Program :=
  P256IsZeroNSAsm.p256IsZeroN_prog

def p256IsZeroNFunction : String :=
  "p256_is_zero_n:\n" ++ emitProgram p256IsZeroN_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256IsZeroN_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256IsZeroNFunction_eq_prog :
    p256IsZeroNFunction = "p256_is_zero_n:\n" ++ emitProgram p256IsZeroN_prog := rfl

#guard p256IsZeroNFunction.startsWith "p256_is_zero_n:\n"
#guard p256IsZeroN_prog.length = 12
/-- a0 = 1 iff the two 32-byte buffers at a0/a1 are equal. Leaf. -/
def p256Eq32_prog : Program :=
  P256Eq32SAsm.p256Eq32_prog

def p256Eq32Function : String :=
  "p256_eq32:\n" ++ emitProgram p256Eq32_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256Eq32_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256Eq32Function_eq_prog :
    p256Eq32Function = "p256_eq32:\n" ++ emitProgram p256Eq32_prog := rfl

#guard p256Eq32Function.startsWith "p256_eq32:\n"
#guard p256Eq32_prog.length = 15
/-- a0 = 1 iff the 32-byte BE integer at a0 is strictly less than the
    one at a1. Leaf. -/
def p256LtBe_prog : Program :=
  [ .LI .x7 (32 : Word),
    .MV .x5 .x10,
    .MV .x6 .x11,
    .BEQ .x7 .x0 (44 : BitVec 13),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BLTU .x28 .x29 (24 : BitVec 13),
    .BLTU .x29 .x28 (28 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .JAL .x0 (-32 : BitVec 21),
    .LI .x10 (1 : Word),
    .JALR .x0 .x1 (0 : BitVec 12),
    .LI .x10 (0 : Word),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def p256LtBeFunction : String :=
  "p256_lt_be:\n" ++ emitProgram p256LtBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256LtBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256LtBeFunction_eq_prog :
    p256LtBeFunction = "p256_lt_be:\n" ++ emitProgram p256LtBe_prog := rfl

#guard p256LtBeFunction.startsWith "p256_lt_be:\n"
#guard p256LtBe_prog.length = 16
/-- Convert a 32-byte BE buffer (a0, any alignment) into four LE u64
    limbs (a1, 8-aligned), LSB limb first. Leaf. -/
def p256BeToLe_prog : Program :=
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

def p256BeToLeFunction : String :=
  "p256_be_to_le:\n" ++ emitProgram p256BeToLe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256BeToLe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256BeToLeFunction_eq_prog :
    p256BeToLeFunction = "p256_be_to_le:\n" ++ emitProgram p256BeToLe_prog := rfl

#guard p256BeToLeFunction.startsWith "p256_be_to_le:\n"
#guard p256BeToLe_prog.length = 20
/-- Convert four LE u64 limbs (a0, 8-aligned) into a 32-byte BE buffer
    (a1, any alignment). Inverse of `p256_be_to_le`. Leaf. -/
def p256LeToBe_prog : Program :=
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

def p256LeToBeFunction : String :=
  "p256_le_to_be:\n" ++ emitProgram p256LeToBe_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `p256LeToBe_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem p256LeToBeFunction_eq_prog :
    p256LeToBeFunction = "p256_le_to_be:\n" ++ emitProgram p256LeToBe_prog := rfl

#guard p256LeToBeFunction.startsWith "p256_le_to_be:\n"
#guard p256LeToBe_prog.length = 19
/-- Fused Arith256Mod op: a0/a1 = 32-byte BE operands (staged into
    `p256_le_a`/`p256_le_b`), a2 = 32-byte BE output, a3 = the
    {a,b,c,module,d} parameter block selecting the operation
    (mul/add/sub mod p, mul mod n). -/
def p256OpWith_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x11,
    .MV .x9 .x12,
    .MV .x18 .x13,
    .AUIPC .x11 (laHi GuestAddrs.p256_le_a (GuestAddrs.p256_op_with + 32)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_le_a (GuestAddrs.p256_op_with + 32)),
    .JAL .x1 (jalOff GuestAddrs.p256_be_to_le (GuestAddrs.p256_op_with + 40)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.p256_le_b (GuestAddrs.p256_op_with + 48)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_le_b (GuestAddrs.p256_op_with + 48)),
    .JAL .x1 (jalOff GuestAddrs.p256_be_to_le (GuestAddrs.p256_op_with + 56)),
    .MV .x5 .x18,
    .CSRS (2050 : BitVec 12) .x5,
    .AUIPC .x10 (laHi GuestAddrs.p256_le_d (GuestAddrs.p256_op_with + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_le_d (GuestAddrs.p256_op_with + 68)),
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.p256_le_to_be (GuestAddrs.p256_op_with + 80)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256OpWith_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256OpWith_relocs : RelocTable :=
  [ (8, .la .x11 "p256_le_a"),
    (10, .jal .x1 "p256_be_to_le"),
    (12, .la .x11 "p256_le_b"),
    (14, .jal .x1 "p256_be_to_le"),
    (17, .la .x10 "p256_le_d"),
    (20, .jal .x1 "p256_le_to_be") ]

def p256OpWithFunction : String :=
  "p256_op_with:\n" ++ emitProgramR p256OpWith_prog p256OpWith_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256OpWith_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256OpWithFunction_eq_prog :
    p256OpWithFunction = "p256_op_with:\n" ++ emitProgramR p256OpWith_prog p256OpWith_relocs := rfl

#guard p256OpWithFunction.startsWith "p256_op_with:\n"
#guard p256OpWith_prog.length = 27
/-- Modular pow: a0 = base (32 B BE, reduced), a1 = 32-byte BE
    exponent, a2 = output, a3 = the mul parameter block (mod p or
    mod n). MSB-first square-and-multiply; acc in `p256_acc` (output
    must not alias the base or `p256_acc`). -/
def p256Pow_prog : Program :=
  [ .ADDI .x2 .x2 (-64 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x22 .x13,
    .AUIPC .x10 (laHi GuestAddrs.p256_one_be (GuestAddrs.p256_pow + 52)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_one_be (GuestAddrs.p256_pow + 52)),
    .AUIPC .x11 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 60)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 60)),
    .LI .x12 (32 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_pow + 72)),
    .LI .x19 (0 : Word),
    .LI .x5 (32 : Word),
    .BGEU .x19 .x5 (104 : BitVec 13),
    .ADD .x5 .x9 .x19,
    .LBU .x20 .x5 (0 : BitVec 12),
    .LI .x21 (128 : Word),
    .BEQ .x21 .x0 (80 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 104)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 104)),
    .AUIPC .x11 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 112)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 112)),
    .AUIPC .x12 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 120)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 120)),
    .MV .x13 .x22,
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_pow + 132)),
    .AND .x5 .x20 .x21,
    .BEQ .x5 .x0 (32 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 144)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 156)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 156)),
    .MV .x13 .x22,
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_pow + 168)),
    .SRLI .x21 .x21 (1 : BitVec 6),
    .JAL .x0 (-76 : BitVec 21),
    .ADDI .x19 .x19 (1 : BitVec 12),
    .JAL .x0 (-104 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.p256_acc (GuestAddrs.p256_pow + 188)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_acc (GuestAddrs.p256_pow + 188)),
    .MV .x11 .x18,
    .LI .x12 (32 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_pow + 204)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (64 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256Pow_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256Pow_relocs : RelocTable :=
  [ (13, .la .x10 "p256_one_be"),
    (15, .la .x11 "p256_acc"),
    (18, .jal .x1 "p256_copy_n"),
    (26, .la .x10 "p256_acc"),
    (28, .la .x11 "p256_acc"),
    (30, .la .x12 "p256_acc"),
    (33, .jal .x1 "p256_op_with"),
    (36, .la .x10 "p256_acc"),
    (39, .la .x12 "p256_acc"),
    (42, .jal .x1 "p256_op_with"),
    (47, .la .x10 "p256_acc"),
    (51, .jal .x1 "p256_copy_n") ]

def p256PowFunction : String :=
  "p256_pow:\n" ++ emitProgramR p256Pow_prog p256Pow_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256Pow_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256PowFunction_eq_prog :
    p256PowFunction = "p256_pow:\n" ++ emitProgramR p256Pow_prog p256Pow_relocs := rfl

#guard p256PowFunction.startsWith "p256_pow:\n"
#guard p256Pow_prog.length = 62
/-- Shared chord/tangent tail: with lambda staged at `p256_lam`,
    a0 = P, a1 = Q, a2 = out (64 B BE; out may alias P/Q — the result
    is staged through t1/t2 before the output copy):
    x3 = lam^2 - x1 - x2; y3 = lam*(x1 - x3) - y1. -/
def p256ChordTail_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .AUIPC .x10 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 32)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 32)),
    .AUIPC .x11 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 40)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 40)),
    .AUIPC .x12 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 48)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 48)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_chord_tail + 56)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_chord_tail + 56)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 64)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 68)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 68)),
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 80)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 80)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 88)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 88)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 96)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 100)),
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 112)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 112)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 120)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 120)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 128)),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 136)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 136)),
    .AUIPC .x12 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 144)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 152)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 152)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 160)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 164)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 164)),
    .AUIPC .x11 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 172)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_chord_tail + 172)),
    .AUIPC .x12 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 180)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_chord_tail + 188)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_chord_tail + 188)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 196)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 200)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 200)),
    .ADDI .x11 .x8 (32 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 212)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 220)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_chord_tail + 220)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_chord_tail + 228)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 232)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t1 (GuestAddrs.p256_chord_tail + 232)),
    .MV .x11 .x18,
    .LI .x12 (32 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_chord_tail + 248)),
    .AUIPC .x10 (laHi GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 252)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_t2 (GuestAddrs.p256_chord_tail + 252)),
    .ADDI .x11 .x18 (32 : BitVec 12),
    .LI .x12 (32 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_chord_tail + 268)),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256ChordTail_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256ChordTail_relocs : RelocTable :=
  [ (8, .la .x10 "p256_lam"),
    (10, .la .x11 "p256_lam"),
    (12, .la .x12 "p256_t1"),
    (14, .la .x13 "p256_pb_mul_p"),
    (16, .jal .x1 "p256_op_with"),
    (17, .la .x10 "p256_t1"),
    (20, .la .x12 "p256_t1"),
    (22, .la .x13 "p256_pb_sub_p"),
    (24, .jal .x1 "p256_op_with"),
    (25, .la .x10 "p256_t1"),
    (28, .la .x12 "p256_t1"),
    (30, .la .x13 "p256_pb_sub_p"),
    (32, .jal .x1 "p256_op_with"),
    (34, .la .x11 "p256_t1"),
    (36, .la .x12 "p256_t2"),
    (38, .la .x13 "p256_pb_sub_p"),
    (40, .jal .x1 "p256_op_with"),
    (41, .la .x10 "p256_t2"),
    (43, .la .x11 "p256_lam"),
    (45, .la .x12 "p256_t2"),
    (47, .la .x13 "p256_pb_mul_p"),
    (49, .jal .x1 "p256_op_with"),
    (50, .la .x10 "p256_t2"),
    (53, .la .x12 "p256_t2"),
    (55, .la .x13 "p256_pb_sub_p"),
    (57, .jal .x1 "p256_op_with"),
    (58, .la .x10 "p256_t1"),
    (62, .jal .x1 "p256_copy_n"),
    (63, .la .x10 "p256_t2"),
    (67, .jal .x1 "p256_copy_n") ]

def p256ChordTailFunction : String :=
  "p256_chord_tail:\n" ++ emitProgramR p256ChordTail_prog p256ChordTail_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256ChordTail_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256ChordTailFunction_eq_prog :
    p256ChordTailFunction = "p256_chord_tail:\n" ++ emitProgramR p256ChordTail_prog p256ChordTail_relocs := rfl

#guard p256ChordTailFunction.startsWith "p256_chord_tail:\n"
#guard p256ChordTail_prog.length = 74
/-- Double an affine point: a0 = input, a1 = output (64 B BE, may
    alias). Returns a0 = 1 when the result is infinity (y = 0; output
    zeroed). lam = (3x^2 + a) / 2y. -/
def p256PointDbl_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .ADDI .x10 .x8 (32 : BitVec 12),
    .LI .x11 (32 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_is_zero_n (GuestAddrs.p256_point_dbl + 32)),
    .BEQ .x10 .x0 (64 : BitVec 13),
    .MV .x10 .x9,
    .LI .x5 (8 : Word),
    .SB .x10 .x0 (0 : BitVec 12),
    .SB .x10 .x0 (1 : BitVec 12),
    .SB .x10 .x0 (2 : BitVec 12),
    .SB .x10 .x0 (3 : BitVec 12),
    .SB .x10 .x0 (4 : BitVec 12),
    .SB .x10 .x0 (5 : BitVec 12),
    .SB .x10 .x0 (6 : BitVec 12),
    .SB .x10 .x0 (7 : BitVec 12),
    .ADDI .x10 .x10 (8 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-40 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (260 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 108)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 108)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 116)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 116)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 124)),
    .AUIPC .x10 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 128)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 128)),
    .AUIPC .x11 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 136)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 136)),
    .AUIPC .x12 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 144)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 144)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 152)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 152)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 160)),
    .AUIPC .x10 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 164)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 164)),
    .AUIPC .x11 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 172)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 172)),
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 180)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 180)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 188)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 188)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 196)),
    .AUIPC .x10 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 200)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 200)),
    .AUIPC .x11 (laHi GuestAddrs.p256_a_be (GuestAddrs.p256_point_dbl + 208)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_a_be (GuestAddrs.p256_point_dbl + 208)),
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 216)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 216)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 224)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 224)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 232)),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .ADDI .x11 .x8 (32 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 244)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 244)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 252)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_add_p (GuestAddrs.p256_point_dbl + 252)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 260)),
    .AUIPC .x10 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 264)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_dbl + 264)),
    .AUIPC .x11 (laHi GuestAddrs.p256_pm2_be (GuestAddrs.p256_point_dbl + 272)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_pm2_be (GuestAddrs.p256_point_dbl + 272)),
    .AUIPC .x12 (laHi GuestAddrs.p256_inv_out (GuestAddrs.p256_point_dbl + 280)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_inv_out (GuestAddrs.p256_point_dbl + 280)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 288)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 288)),
    .JAL .x1 (jalOff GuestAddrs.p256_pow (GuestAddrs.p256_point_dbl + 296)),
    .AUIPC .x10 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 300)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 300)),
    .AUIPC .x11 (laHi GuestAddrs.p256_inv_out (GuestAddrs.p256_point_dbl + 308)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_inv_out (GuestAddrs.p256_point_dbl + 308)),
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 316)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_dbl + 316)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 324)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_dbl + 324)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_dbl + 332)),
    .MV .x10 .x8,
    .MV .x11 .x8,
    .MV .x12 .x9,
    .JAL .x1 (jalOff GuestAddrs.p256_chord_tail (GuestAddrs.p256_point_dbl + 348)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256PointDbl_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256PointDbl_relocs : RelocTable :=
  [ (8, .jal .x1 "p256_is_zero_n"),
    (27, .la .x12 "p256_lam"),
    (29, .la .x13 "p256_pb_mul_p"),
    (31, .jal .x1 "p256_op_with"),
    (32, .la .x10 "p256_lam"),
    (34, .la .x11 "p256_lam"),
    (36, .la .x12 "p256_den"),
    (38, .la .x13 "p256_pb_add_p"),
    (40, .jal .x1 "p256_op_with"),
    (41, .la .x10 "p256_den"),
    (43, .la .x11 "p256_lam"),
    (45, .la .x12 "p256_lam"),
    (47, .la .x13 "p256_pb_add_p"),
    (49, .jal .x1 "p256_op_with"),
    (50, .la .x10 "p256_lam"),
    (52, .la .x11 "p256_a_be"),
    (54, .la .x12 "p256_lam"),
    (56, .la .x13 "p256_pb_add_p"),
    (58, .jal .x1 "p256_op_with"),
    (61, .la .x12 "p256_den"),
    (63, .la .x13 "p256_pb_add_p"),
    (65, .jal .x1 "p256_op_with"),
    (66, .la .x10 "p256_den"),
    (68, .la .x11 "p256_pm2_be"),
    (70, .la .x12 "p256_inv_out"),
    (72, .la .x13 "p256_pb_mul_p"),
    (74, .jal .x1 "p256_pow"),
    (75, .la .x10 "p256_lam"),
    (77, .la .x11 "p256_inv_out"),
    (79, .la .x12 "p256_lam"),
    (81, .la .x13 "p256_pb_mul_p"),
    (83, .jal .x1 "p256_op_with"),
    (87, .jal .x1 "p256_chord_tail") ]

def p256PointDblFunction : String :=
  "p256_point_dbl:\n" ++ emitProgramR p256PointDbl_prog p256PointDbl_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256PointDbl_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256PointDblFunction_eq_prog :
    p256PointDblFunction = "p256_point_dbl:\n" ++ emitProgramR p256PointDbl_prog p256PointDbl_relocs := rfl

#guard p256PointDblFunction.startsWith "p256_point_dbl:\n"
#guard p256PointDbl_prog.length = 94
/-- Add two FINITE affine points: a0 = P, a1 = Q, a2 = out (64 B BE;
    out may alias). Equal x with equal y doubles; equal x with
    opposite y returns infinity (a0 = 1, output zeroed). Infinity
    INPUTS are the caller's job (tracked in flags, as in the
    secp256k1 scalar-mul shape). -/
def p256PointAdd_prog : Program :=
  [ .ADDI .x2 .x2 (-40 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .JAL .x1 (jalOff GuestAddrs.p256_eq32 (GuestAddrs.p256_point_add + 40)),
    .BEQ .x10 .x0 (36 : BitVec 13),
    .ADDI .x10 .x8 (32 : BitVec 12),
    .ADDI .x11 .x9 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.p256_eq32 (GuestAddrs.p256_point_add + 56)),
    .BEQ .x10 .x0 (172 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.p256_point_dbl (GuestAddrs.p256_point_add + 72)),
    .JAL .x0 (184 : BitVec 21),
    .ADDI .x10 .x9 (32 : BitVec 12),
    .ADDI .x11 .x8 (32 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 88)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 88)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_point_add + 96)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_point_add + 96)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_add + 104)),
    .MV .x10 .x9,
    .MV .x11 .x8,
    .AUIPC .x12 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_add + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_add + 116)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_point_add + 124)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_sub_p (GuestAddrs.p256_point_add + 124)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_add + 132)),
    .AUIPC .x10 (laHi GuestAddrs.p256_den (GuestAddrs.p256_point_add + 136)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_den (GuestAddrs.p256_point_add + 136)),
    .AUIPC .x11 (laHi GuestAddrs.p256_pm2_be (GuestAddrs.p256_point_add + 144)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_pm2_be (GuestAddrs.p256_point_add + 144)),
    .AUIPC .x12 (laHi GuestAddrs.p256_inv_out (GuestAddrs.p256_point_add + 152)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_inv_out (GuestAddrs.p256_point_add + 152)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_add + 160)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_add + 160)),
    .JAL .x1 (jalOff GuestAddrs.p256_pow (GuestAddrs.p256_point_add + 168)),
    .AUIPC .x10 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 172)),
    .AUIPC .x11 (laHi GuestAddrs.p256_inv_out (GuestAddrs.p256_point_add + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.p256_inv_out (GuestAddrs.p256_point_add + 180)),
    .AUIPC .x12 (laHi GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 188)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_lam (GuestAddrs.p256_point_add + 188)),
    .AUIPC .x13 (laHi GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_add + 196)),
    .ADDI .x13 .x13 (laLo GuestAddrs.p256_pb_mul_p (GuestAddrs.p256_point_add + 196)),
    .JAL .x1 (jalOff GuestAddrs.p256_op_with (GuestAddrs.p256_point_add + 204)),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.p256_chord_tail (GuestAddrs.p256_point_add + 220)),
    .LI .x10 (0 : Word),
    .JAL .x0 (32 : BitVec 21),
    .MV .x10 .x18,
    .LI .x11 (64 : Word),
    .SB .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x11 .x11 (-1 : BitVec 12),
    .BNE .x11 .x0 (-12 : BitVec 13),
    .LI .x10 (1 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (40 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256PointAdd_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256PointAdd_relocs : RelocTable :=
  [ (10, .jal .x1 "p256_eq32"),
    (14, .jal .x1 "p256_eq32"),
    (18, .jal .x1 "p256_point_dbl"),
    (22, .la .x12 "p256_lam"),
    (24, .la .x13 "p256_pb_sub_p"),
    (26, .jal .x1 "p256_op_with"),
    (29, .la .x12 "p256_den"),
    (31, .la .x13 "p256_pb_sub_p"),
    (33, .jal .x1 "p256_op_with"),
    (34, .la .x10 "p256_den"),
    (36, .la .x11 "p256_pm2_be"),
    (38, .la .x12 "p256_inv_out"),
    (40, .la .x13 "p256_pb_mul_p"),
    (42, .jal .x1 "p256_pow"),
    (43, .la .x10 "p256_lam"),
    (45, .la .x11 "p256_inv_out"),
    (47, .la .x12 "p256_lam"),
    (49, .la .x13 "p256_pb_mul_p"),
    (51, .jal .x1 "p256_op_with"),
    (55, .jal .x1 "p256_chord_tail") ]

def p256PointAddFunction : String :=
  "p256_point_add:\n" ++ emitProgramR p256PointAdd_prog p256PointAdd_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256PointAdd_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256PointAddFunction_eq_prog :
    p256PointAddFunction = "p256_point_add:\n" ++ emitProgramR p256PointAdd_prog p256PointAdd_relocs := rfl

#guard p256PointAddFunction.startsWith "p256_point_add:\n"
#guard p256PointAdd_prog.length = 71
/-- Multiply an affine point by a 32-byte BE scalar (MSB-first
    double-and-add): a0 = scalar, a1 = base point, a2 = output (must
    not alias the base). Returns a0 = 1 when the result is infinity
    (output zeroed). -/
def p256ScalarMul_prog : Program :=
  [ .ADDI .x2 .x2 (-72 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .SD .x2 .x19 (32 : BitVec 12),
    .SD .x2 .x20 (40 : BitVec 12),
    .SD .x2 .x21 (48 : BitVec 12),
    .SD .x2 .x22 (56 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x10 .x18,
    .LI .x5 (64 : Word),
    .SB .x10 .x0 (0 : BitVec 12),
    .ADDI .x10 .x10 (1 : BitVec 12),
    .ADDI .x5 .x5 (-1 : BitVec 12),
    .BNE .x5 .x0 (-12 : BitVec 13),
    .LI .x19 (1 : Word),
    .LI .x20 (0 : Word),
    .LI .x5 (32 : Word),
    .BGEU .x20 .x5 (136 : BitVec 13),
    .ADD .x5 .x8 .x20,
    .LBU .x21 .x5 (0 : BitVec 12),
    .LI .x22 (128 : Word),
    .BEQ .x22 .x0 (112 : BitVec 13),
    .BNE .x19 .x0 (20 : BitVec 13),
    .MV .x10 .x18,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.p256_point_dbl (GuestAddrs.p256_scalar_mul + 116)),
    .MV .x19 .x10,
    .AND .x5 .x21 .x22,
    .BEQ .x5 .x0 (76 : BitVec 13),
    .BEQ .x19 .x0 (28 : BitVec 13),
    .MV .x10 .x9,
    .MV .x11 .x18,
    .LI .x12 (64 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_scalar_mul + 148)),
    .LI .x19 (0 : Word),
    .JAL .x0 (48 : BitVec 21),
    .MV .x10 .x18,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.p256_ptmp (GuestAddrs.p256_scalar_mul + 168)),
    .ADDI .x12 .x12 (laLo GuestAddrs.p256_ptmp (GuestAddrs.p256_scalar_mul + 168)),
    .JAL .x1 (jalOff GuestAddrs.p256_point_add (GuestAddrs.p256_scalar_mul + 176)),
    .MV .x19 .x10,
    .AUIPC .x10 (laHi GuestAddrs.p256_ptmp (GuestAddrs.p256_scalar_mul + 184)),
    .ADDI .x10 .x10 (laLo GuestAddrs.p256_ptmp (GuestAddrs.p256_scalar_mul + 184)),
    .MV .x11 .x18,
    .LI .x12 (64 : Word),
    .JAL .x1 (jalOff GuestAddrs.p256_copy_n (GuestAddrs.p256_scalar_mul + 200)),
    .SRLI .x22 .x22 (1 : BitVec 6),
    .JAL .x0 (-108 : BitVec 21),
    .ADDI .x20 .x20 (1 : BitVec 12),
    .JAL .x0 (-136 : BitVec 21),
    .MV .x10 .x19,
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .ADDI .x2 .x2 (72 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `p256ScalarMul_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def p256ScalarMul_relocs : RelocTable :=
  [ (29, .jal .x1 "p256_point_dbl"),
    (37, .jal .x1 "p256_copy_n"),
    (42, .la .x12 "p256_ptmp"),
    (44, .jal .x1 "p256_point_add"),
    (46, .la .x10 "p256_ptmp"),
    (50, .jal .x1 "p256_copy_n") ]

def p256ScalarMulFunction : String :=
  "p256_scalar_mul:\n" ++ emitProgramR p256ScalarMul_prog p256ScalarMul_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `p256ScalarMul_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem p256ScalarMulFunction_eq_prog :
    p256ScalarMulFunction = "p256_scalar_mul:\n" ++ emitProgramR p256ScalarMul_prog p256ScalarMul_relocs := rfl

#guard p256ScalarMulFunction.startsWith "p256_scalar_mul:\n"
#guard p256ScalarMul_prog.length = 66
/-- Real P256VERIFY kernel (see the module docstring for the ABI and
    the gate list). -/
def zkvmSecp256r1VerifyRealFunction : String :=
  ".globl zkvm_secp256r1_verify\n" ++
  "zkvm_secp256r1_verify:\n" ++
  "  addi sp, sp, -56\n" ++
  "  sd ra, 0(sp); sd s0, 8(sp); sd s1, 16(sp); sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp); sd s4, 40(sp); sd s5, 48(sp)\n" ++
  "  mv s0, a0                      # msg hash (32 B)\n" ++
  "  mv s1, a1                      # sig r || s (64 B)\n" ++
  "  mv s2, a2                      # pubkey qx || qy (64 B)\n" ++
  "  mv s3, a3                      # verified byte ptr\n" ++
  -- 0 < r < n
  "  mv a0, s1\n" ++
  "  li a1, 32\n" ++
  "  jal ra, p256_is_zero_n\n" ++
  "  bnez a0, .Lp256v_invalid\n" ++
  "  mv a0, s1\n" ++
  "  la a1, p256_n_be\n" ++
  "  jal ra, p256_lt_be\n" ++
  "  beqz a0, .Lp256v_invalid\n" ++
  -- 0 < s < n
  "  addi a0, s1, 32\n" ++
  "  li a1, 32\n" ++
  "  jal ra, p256_is_zero_n\n" ++
  "  bnez a0, .Lp256v_invalid\n" ++
  "  addi a0, s1, 32\n" ++
  "  la a1, p256_n_be\n" ++
  "  jal ra, p256_lt_be\n" ++
  "  beqz a0, .Lp256v_invalid\n" ++
  -- qx < p, qy < p, (qx, qy) != (0, 0)
  "  mv a0, s2\n" ++
  "  la a1, p256_p_be\n" ++
  "  jal ra, p256_lt_be\n" ++
  "  beqz a0, .Lp256v_invalid\n" ++
  "  addi a0, s2, 32\n" ++
  "  la a1, p256_p_be\n" ++
  "  jal ra, p256_lt_be\n" ++
  "  beqz a0, .Lp256v_invalid\n" ++
  "  mv a0, s2\n" ++
  "  li a1, 64\n" ++
  "  jal ra, p256_is_zero_n\n" ++
  "  bnez a0, .Lp256v_invalid\n" ++
  -- on-curve: qy^2 == qx^3 + a*qx + b (cofactor 1, so this is the
  -- whole subgroup check)
  "  mv a0, s2\n" ++
  "  mv a1, s2\n" ++
  "  la a2, p256_t1\n" ++
  "  la a3, p256_pb_mul_p\n" ++
  "  jal ra, p256_op_with           # t1 = qx^2\n" ++
  "  la a0, p256_t1\n" ++
  "  mv a1, s2\n" ++
  "  la a2, p256_t1\n" ++
  "  la a3, p256_pb_mul_p\n" ++
  "  jal ra, p256_op_with           # t1 = qx^3\n" ++
  "  mv a0, s2\n" ++
  "  la a1, p256_a_be\n" ++
  "  la a2, p256_t2\n" ++
  "  la a3, p256_pb_mul_p\n" ++
  "  jal ra, p256_op_with           # t2 = a*qx\n" ++
  "  la a0, p256_t1\n" ++
  "  la a1, p256_t2\n" ++
  "  la a2, p256_t1\n" ++
  "  la a3, p256_pb_add_p\n" ++
  "  jal ra, p256_op_with           # t1 = qx^3 + a*qx\n" ++
  "  la a0, p256_t1\n" ++
  "  la a1, p256_b_be\n" ++
  "  la a2, p256_t1\n" ++
  "  la a3, p256_pb_add_p\n" ++
  "  jal ra, p256_op_with           # t1 = qx^3 + a*qx + b\n" ++
  "  addi a0, s2, 32\n" ++
  "  addi a1, s2, 32\n" ++
  "  la a2, p256_t2\n" ++
  "  la a3, p256_pb_mul_p\n" ++
  "  jal ra, p256_op_with           # t2 = qy^2\n" ++
  "  la a0, p256_t1\n" ++
  "  la a1, p256_t2\n" ++
  "  jal ra, p256_eq32\n" ++
  "  beqz a0, .Lp256v_invalid\n" ++
  -- u1 = e * s^-1 mod n, u2 = r * s^-1 mod n (e is the raw hash; the
  -- mod-n reduction happens inside the Arith256Mod multiplication)
  "  addi a0, s1, 32\n" ++
  "  la a1, p256_nm2_be\n" ++
  "  la a2, p256_sinv\n" ++
  "  la a3, p256_pb_mul_n\n" ++
  "  jal ra, p256_pow               # sinv = s^(n-2) mod n\n" ++
  "  mv a0, s0\n" ++
  "  la a1, p256_sinv\n" ++
  "  la a2, p256_u1\n" ++
  "  la a3, p256_pb_mul_n\n" ++
  "  jal ra, p256_op_with\n" ++
  "  mv a0, s1\n" ++
  "  la a1, p256_sinv\n" ++
  "  la a2, p256_u2\n" ++
  "  la a3, p256_pb_mul_n\n" ++
  "  jal ra, p256_op_with\n" ++
  -- R = u1*G + u2*Q (u2 != 0 since r, sinv != 0; u1 may be 0)\n
  "  la a0, p256_u1\n" ++
  "  la a1, p256_gen_be\n" ++
  "  la a2, p256_p1\n" ++
  "  jal ra, p256_scalar_mul\n" ++
  "  mv s4, a0                      # 1 = u1*G at infinity\n" ++
  "  la a0, p256_u2\n" ++
  "  mv a1, s2\n" ++
  "  la a2, p256_p2\n" ++
  "  jal ra, p256_scalar_mul\n" ++
  "  mv s5, a0                      # 1 = u2*Q at infinity\n" ++
  "  and t0, s4, s5\n" ++
  "  bnez t0, .Lp256v_invalid       # R = inf\n" ++
  "  beqz s4, .Lp256v_have_p1\n" ++
  "  la a0, p256_p2\n" ++
  "  la a1, p256_p1\n" ++
  "  li a2, 64\n" ++
  "  jal ra, p256_copy_n            # R = u2*Q\n" ++
  "  j .Lp256v_have_r\n" ++
  ".Lp256v_have_p1:\n" ++
  "  bnez s5, .Lp256v_have_r        # R = u1*G already in p256_p1\n" ++
  "  la a0, p256_p1\n" ++
  "  la a1, p256_p2\n" ++
  "  la a2, p256_p1\n" ++
  "  jal ra, p256_point_add\n" ++
  "  bnez a0, .Lp256v_invalid       # u1*G + u2*Q = inf\n" ++
  ".Lp256v_have_r:\n" ++
  -- valid iff R.x mod n == r
  "  la a0, p256_p1\n" ++
  "  la a1, p256_one_be\n" ++
  "  la a2, p256_v\n" ++
  "  la a3, p256_pb_mul_n\n" ++
  "  jal ra, p256_op_with           # v = R.x mod n\n" ++
  "  la a0, p256_v\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, p256_eq32\n" ++
  "  sb a0, 0(s3)\n" ++
  "  j .Lp256v_ret\n" ++
  ".Lp256v_invalid:\n" ++
  "  sb zero, 0(s3)\n" ++
  ".Lp256v_ret:\n" ++
  "  li a0, 0\n" ++
  "  ld ra, 0(sp); ld s0, 8(sp); ld s1, 16(sp); ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp); ld s4, 40(sp); ld s5, 48(sp)\n" ++
  "  addi sp, sp, 56\n" ++
  "  ret"

/-- The self-contained P256VERIFY suite. -/
def p256VerifyKernelFunctions : String :=
  p256CopyNFunction ++ "\n" ++
  p256IsZeroNFunction ++ "\n" ++
  p256Eq32Function ++ "\n" ++
  p256LtBeFunction ++ "\n" ++
  p256BeToLeFunction ++ "\n" ++
  p256LeToBeFunction ++ "\n" ++
  p256OpWithFunction ++ "\n" ++
  p256PowFunction ++ "\n" ++
  p256ChordTailFunction ++ "\n" ++
  p256PointDblFunction ++ "\n" ++
  p256PointAddFunction ++ "\n" ++
  p256ScalarMulFunction ++ "\n" ++
  zkvmSecp256r1VerifyRealFunction

/-- Probe: input at `0x40000008` = the raw 160-byte EIP-7951 payload
    `hash(32) || r(32) || s(32) || qx(32) || qy(32)`. Output: status
    u64 at OUTPUT+0, verified byte at OUTPUT+8. -/
def ziskP256VerifyRealProbePrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li s0, 0x40000008\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, s0, 32\n" ++
  "  addi a2, s0, 96\n" ++
  "  li a3, 0xa0010008\n" ++
  "  jal ra, zkvm_secp256r1_verify\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lp256_probe_done\n" ++
  p256VerifyKernelFunctions ++ "\n" ++
  ".Lp256_probe_done:"

def ziskP256VerifyRealProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskP256VerifyRealProbePrologue
  dataAsm     := ".section .data\n" ++ p256VerifyDataFragment
}

end EvmAsm.Codegen
