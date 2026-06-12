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
def bn254FieldBeToLeFunction : String :=
  "bnf_be_to_le:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lbnf_b2l_quad:\n" ++
  "  li t1, 24\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a0, t1             # BE offset of the limb's MSB\n" ++
  "  li t3, 0\n" ++
  "  li t4, 8\n" ++
  ".Lbnf_b2l_byte:\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  or t3, t3, t5\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lbnf_b2l_byte\n" ++
  "  slli t2, t0, 3\n" ++
  "  add t2, a1, t2\n" ++
  "  sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 4\n" ++
  "  bne t0, t1, .Lbnf_b2l_quad\n" ++
  "  ret"

/-- Convert four little-endian u64 limbs (`a0`, 8-aligned) into a 32-byte
    big-endian buffer (`a1`, byte-addressed, any alignment). Inverse of
    `bnf_be_to_le`. Leaf helper; clobbers only `t` regs. -/
def bn254FieldLeToBeFunction : String :=
  "bnf_le_to_be:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lbnf_l2b_quad:\n" ++
  "  slli t1, t0, 3\n" ++
  "  add t2, a0, t1\n" ++
  "  ld t3, 0(t2)\n" ++
  "  li t1, 31\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a1, t1             # BE offset of the limb's LSB\n" ++
  "  li t4, 8\n" ++
  ".Lbnf_l2b_byte:\n" ++
  "  andi t5, t3, 0xff\n" ++
  "  sb t5, 0(t1)\n" ++
  "  srli t3, t3, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lbnf_l2b_byte\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 4\n" ++
  "  bne t0, t1, .Lbnf_l2b_quad\n" ++
  "  ret"

/-- Return a0 = 1 iff the 32-byte buffer at a0 is all-zero. Leaf helper. -/
def bn254FieldIsZeroFunction : String :=
  "bnf_is_zero32:\n" ++
  "  li t0, 32\n" ++
  "  mv t1, a0\n" ++
  ".Lbnf_is_zero_loop:\n" ++
  "  beqz t0, .Lbnf_is_zero_yes\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  bnez t2, .Lbnf_is_zero_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lbnf_is_zero_loop\n" ++
  ".Lbnf_is_zero_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lbnf_is_zero_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- Return a0 = 1 iff the two 32-byte buffers at a0 and a1 are equal. -/
def bn254FieldEq32Function : String :=
  "bnf_eq32:\n" ++
  "  li t0, 32\n" ++
  "  mv t1, a0\n" ++
  "  mv t2, a1\n" ++
  ".Lbnf_eq_loop:\n" ++
  "  beqz t0, .Lbnf_eq_yes\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lbnf_eq_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lbnf_eq_loop\n" ++
  ".Lbnf_eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lbnf_eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- Return a0 = 1 iff the 32-byte big-endian integer at a0 is `< p`
    (the EIP-196 coordinate range check). Leaf helper. -/
def bn254FieldLtPFunction : String :=
  "bnf_lt_p:\n" ++
  "  la t0, bnf_p_be\n" ++
  "  li t1, 32\n" ++
  "  mv t2, a0\n" ++
  ".Lbnf_ltp_loop:\n" ++
  "  beqz t1, .Lbnf_ltp_no       # equal => not less\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lbnf_ltp_yes\n" ++
  "  bltu t4, t3, .Lbnf_ltp_no\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lbnf_ltp_loop\n" ++
  ".Lbnf_ltp_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lbnf_ltp_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

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
