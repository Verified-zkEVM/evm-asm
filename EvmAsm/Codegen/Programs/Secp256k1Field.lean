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
import EvmAsm.Codegen.Programs.U256

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
  "secp256k1_sqrt_exp_be:\n" ++
  "  .byte 0x3f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xfb,0xff,0xff,0xff,0x0c\n" ++
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
def secp256k1FieldCopy32Function : String :=
  "secf_copy32:\n" ++
  "  ld t0,  0(a0); sd t0,  0(a1)\n" ++
  "  ld t0,  8(a0); sd t0,  8(a1)\n" ++
  "  ld t0, 16(a0); sd t0, 16(a1)\n" ++
  "  ld t0, 24(a0); sd t0, 24(a1)\n" ++
  "  ret"


/-- Zero a 32-byte buffer. Leaf helper. -/
def secp256k1FieldZero32Function : String :=
  "secf_zero32:\n" ++
  "  sd zero,  0(a0)\n" ++
  "  sd zero,  8(a0)\n" ++
  "  sd zero, 16(a0)\n" ++
  "  sd zero, 24(a0)\n" ++
  "  ret"

/-- Convert a 32-byte big-endian buffer (`a0`, byte-addressed, any alignment)
    into four little-endian u64 limbs (`a1`, 8-aligned), least-significant
    limb first — the ziskemu accelerator operand format. Leaf helper;
    clobbers only `t` registers. -/
def secp256k1FieldBeToLeFunction : String :=
  "secf_be_to_le:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lsecf_b2l_quad:\n" ++
  "  li t1, 24\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a0, t1             # BE offset of the limb's MSB\n" ++
  "  li t3, 0\n" ++
  "  li t4, 8\n" ++
  ".Lsecf_b2l_byte:\n" ++
  "  slli t3, t3, 8\n" ++
  "  lbu t5, 0(t1)\n" ++
  "  or t3, t3, t5\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lsecf_b2l_byte\n" ++
  "  slli t2, t0, 3\n" ++
  "  add t2, a1, t2\n" ++
  "  sd t3, 0(t2)\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 4\n" ++
  "  bne t0, t1, .Lsecf_b2l_quad\n" ++
  "  ret"

/-- Convert four little-endian u64 limbs (`a0`, 8-aligned) into a 32-byte
    big-endian buffer (`a1`, byte-addressed, any alignment). Inverse of
    `secf_be_to_le`. Leaf helper; clobbers only `t` registers. -/
def secp256k1FieldLeToBeFunction : String :=
  "secf_le_to_be:\n" ++
  "  li t0, 0                   # limb index\n" ++
  ".Lsecf_l2b_quad:\n" ++
  "  slli t1, t0, 3\n" ++
  "  add t2, a0, t1\n" ++
  "  ld t3, 0(t2)\n" ++
  "  li t1, 31\n" ++
  "  slli t2, t0, 3\n" ++
  "  sub t1, t1, t2\n" ++
  "  add t1, a1, t1             # BE offset of the limb's LSB\n" ++
  "  li t4, 8\n" ++
  ".Lsecf_l2b_byte:\n" ++
  "  andi t5, t3, 0xff\n" ++
  "  sb t5, 0(t1)\n" ++
  "  srli t3, t3, 8\n" ++
  "  addi t1, t1, -1\n" ++
  "  addi t4, t4, -1\n" ++
  "  bnez t4, .Lsecf_l2b_byte\n" ++
  "  addi t0, t0, 1\n" ++
  "  li t1, 4\n" ++
  "  bne t0, t1, .Lsecf_l2b_quad\n" ++
  "  ret"

/-- Return bit `a1` of a 32-byte BE field element, numbering bits from the LSB. -/
def secp256k1FieldGetBitFunction : String :=
  "secf_get_bit_lsb:\n" ++
  "  srli t0, a1, 3             # byte index from the LSB\n" ++
  "  li t1, 31\n" ++
  "  sub t0, t1, t0             # BE byte offset\n" ++
  "  add t0, a0, t0\n" ++
  "  lbu t1, 0(t0)\n" ++
  "  andi t2, a1, 7\n" ++
  "  srl t1, t1, t2\n" ++
  "  andi a0, t1, 1\n" ++
  "  ret"

/-- Return a0 = 1 iff the 32-byte BE buffer at a0 is zero. Leaf helper. -/
def secp256k1FieldIsZeroFunction : String :=
  "secf_is_zero32:\n" ++
  "  li t0, 32\n" ++
  "  mv t1, a0\n" ++
  ".Lsecf_is_zero_loop:\n" ++
  "  beqz t0, .Lsecf_is_zero_yes\n" ++
  "  lbu t2, 0(t1)\n" ++
  "  bnez t2, .Lsecf_is_zero_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lsecf_is_zero_loop\n" ++
  ".Lsecf_is_zero_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lsecf_is_zero_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/-- Return a0 = 1 iff the two 32-byte BE buffers at a0 and a1 are equal. Leaf helper. -/
def secp256k1FieldEq32Function : String :=
  "secf_eq32:\n" ++
  "  li t0, 32\n" ++
  "  mv t1, a0\n" ++
  "  mv t2, a1\n" ++
  ".Lsecf_eq_loop:\n" ++
  "  beqz t0, .Lsecf_eq_yes\n" ++
  "  lbu t3, 0(t1)\n" ++
  "  lbu t4, 0(t2)\n" ++
  "  bne t3, t4, .Lsecf_eq_no\n" ++
  "  addi t1, t1, 1\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, -1\n" ++
  "  j .Lsecf_eq_loop\n" ++
  ".Lsecf_eq_yes:\n" ++
  "  li a0, 1\n" ++
  "  ret\n" ++
  ".Lsecf_eq_no:\n" ++
  "  li a0, 0\n" ++
  "  ret"

/--
  Compare a 32-byte big-endian integer against the secp256k1 field prime.

  Calling convention:
    a0: input pointer
    a1: u64 output pointer; stores 0 for `< p`, 1 for `== p`, 2 for `> p`
    returns a0 = 0.
-/
def secp256k1FieldCmpPFunction : String :=
  "secf_cmp_p:\n" ++
  "  la t0, secp256k1_p_be\n" ++
  "  li t1, 32\n" ++
  "  mv t2, a0\n" ++
  ".Lsecf_cmp_loop:\n" ++
  "  beqz t1, .Lsecf_cmp_equal\n" ++
  "  lbu t3, 0(t2)\n" ++
  "  lbu t4, 0(t0)\n" ++
  "  bltu t3, t4, .Lsecf_cmp_less\n" ++
  "  bltu t4, t3, .Lsecf_cmp_greater\n" ++
  "  addi t2, t2, 1\n" ++
  "  addi t0, t0, 1\n" ++
  "  addi t1, t1, -1\n" ++
  "  j .Lsecf_cmp_loop\n" ++
  ".Lsecf_cmp_less:\n" ++
  "  sd zero, 0(a1)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lsecf_cmp_equal:\n" ++
  "  li t0, 1\n" ++
  "  sd t0, 0(a1)\n" ++
  "  li a0, 0\n" ++
  "  ret\n" ++
  ".Lsecf_cmp_greater:\n" ++
  "  li t0, 2\n" ++
  "  sd t0, 0(a1)\n" ++
  "  li a0, 0\n" ++
  "  ret"

/--
  Reduce a value known to be below `2p` by subtracting p at most once.

  Calling convention:
    a0: input pointer
    a1: output pointer
    returns a0 = 1 if p was subtracted, else 0.
-/
def secp256k1FieldReduceOnceFunction : String :=
  "secf_reduce_once:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secp256k1_p_be\n" ++
  "  la a2, secf_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, secf_cmp\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .Lsecf_reduce_copy\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secp256k1_p_be\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecf_reduce_done\n" ++
  ".Lsecf_reduce_copy:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_copy32\n" ++
  "  li a0, 0\n" ++
  ".Lsecf_reduce_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two field elements modulo p. Inputs and output are 32-byte BE buffers. -/
def secp256k1FieldAddFunction : String :=
  "secf_add_mod_p:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la s3, secf_tmp0\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_add_be\n" ++
  "  mv s4, a0\n" ++
  "  beqz s4, .Lsecf_add_reduce\n" ++
  "  mv a0, s3\n" ++
  "  la a1, secp256k1_c_be\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_add_be\n" ++
  ".Lsecf_add_reduce:\n" ++
  "  mv a0, s3\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_reduce_once\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Subtract two field elements modulo p. Inputs and output are 32-byte BE buffers. -/
def secp256k1FieldSubFunction : String :=
  "secf_sub_mod_p:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la s3, secf_tmp0\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  mv s4, a0\n" ++
  "  beqz s4, .Lsecf_sub_copy\n" ++
  "  mv a0, s3\n" ++
  "  la a1, secp256k1_c_be\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  j .Lsecf_sub_done_status\n" ++
  ".Lsecf_sub_copy:\n" ++
  "  mv a0, s3\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_copy32\n" ++
  ".Lsecf_sub_done_status:\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"



/--
  Multiply two field elements modulo p via the ziskemu `Arith256Mod`
  accelerator: `d = (a*b + 0) mod p` with exact 512-bit intermediate math,
  so unreduced 256-bit inputs are accepted and the output is fully reduced.
  The raw `.4byte 0x8022a073` is `csrs 0x802, t0` (`SYSCALL_ARITH256_MOD_ID`
  with the parameter-block pointer in `t0`), pre-encoded so the
  `-march=rv64imac` toolchain assembles it without `Zicsr` (the same pattern
  as the Keccak-f probe's `.4byte 0x80052073`).
-/
def secp256k1FieldMulFunction : String :=
  "secf_mul_mod_p:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, secf_le_a\n" ++
  "  jal ra, secf_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secf_le_b\n" ++
  "  jal ra, secf_be_to_le\n" ++
  "  la t0, secf_arith_params_p\n" ++
  "  .4byte 0x8022a073           # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  la a0, secf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Square one field element modulo p. -/
def secp256k1FieldSquareFunction : String :=
  "secf_square_mod_p:\n" ++
  "  mv a1, a0\n" ++
  "  jal zero, secf_mul_mod_p"

/-- Modular exponentiation by a 256-bit BE exponent using square-and-multiply. -/
def secp256k1FieldPowFunction : String :=
  "secf_pow_mod_p:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la s4, secf_pow_result\n" ++
  "  la s5, secf_pow_base\n" ++
  "  la a0, secp256k1_one_be\n" ++
  "  mv a1, s4\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s5\n" ++
  "  jal ra, secf_reduce_once\n" ++
  "  li s3, 255\n" ++
  ".Lsecf_pow_loop:\n" ++
  "  mv a0, s4\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_square_mod_p\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s3\n" ++
  "  jal ra, secf_get_bit_lsb\n" ++
  "  beqz a0, .Lsecf_pow_after_mul\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  ".Lsecf_pow_after_mul:\n" ++
  "  beqz s3, .Lsecf_pow_done\n" ++
  "  addi s3, s3, -1\n" ++
  "  j .Lsecf_pow_loop\n" ++
  ".Lsecf_pow_done:\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_copy32\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"


/-- Invert a nonzero field element. Returns a0 = 1 for zero input, else 0. -/
def secp256k1FieldInvFunction : String :=
  "secf_inv_mod_p:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecf_inv_nonzero\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecf_inv_done\n" ++
  ".Lsecf_inv_nonzero:\n" ++
  "  la a0, secp256k1_p_minus_2_be\n" ++
  "  addi a1, sp, 24\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, sp, 24\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, secf_pow_mod_p\n" ++
  "  li a0, 0\n" ++
  ".Lsecf_inv_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"


/-- Square root modulo p. Returns a0 = 1 if no root exists, else 0. -/
def secp256k1FieldSqrtFunction : String :=
  "secf_sqrt_mod_p:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s3, 24(sp)\n" ++
  "  sd s4, 32(sp)\n" ++
  "  sd s5, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  la s4, secf_pow_result\n" ++
  "  la s5, secf_pow_base\n" ++
  "  la a0, secp256k1_one_be\n" ++
  "  mv a1, s4\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s5\n" ++
  "  jal ra, secf_reduce_once\n" ++
  "  li s3, 255\n" ++
  ".Lsecf_sqrt_pow_loop:\n" ++
  "  mv a0, s4\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_square_mod_p\n" ++
  "  li t0, 255\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 254\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 30\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 7\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 6\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 5\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 4\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  li t0, 1\n" ++
  "  beq s3, t0, .Lsecf_sqrt_skip_mul\n" ++
  "  beqz s3, .Lsecf_sqrt_after_mul\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_mul_mod_p\n" ++
  ".Lsecf_sqrt_after_mul:\n" ++
  "  beqz s3, .Lsecf_sqrt_pow_done\n" ++
  ".Lsecf_sqrt_skip_mul:\n" ++
  "  beqz s3, .Lsecf_sqrt_pow_done\n" ++
  "  addi s3, s3, -1\n" ++
  "  j .Lsecf_sqrt_pow_loop\n" ++
  ".Lsecf_sqrt_pow_done:\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s1\n" ++
  "  la a2, secf_pow_verify\n" ++
  "  jal ra, secf_square_mod_p\n" ++
  "  la a0, secf_pow_verify\n" ++
  "  mv a1, s0\n" ++
  "  jal ra, secf_eq32\n" ++
  "  bnez a0, .Lsecf_sqrt_ok\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecf_sqrt_done\n" ++
  ".Lsecf_sqrt_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lsecf_sqrt_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s3, 24(sp)\n" ++
  "  ld s4, 32(sp)\n" ++
  "  ld s5, 40(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"


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
def secp256k1ScalarFieldReduceOnceFunction : String :=
  "secf_reduce_once_n:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secf_n_be\n" ++
  "  la a2, secf_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, secf_cmp\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .Lsecf_reducen_copy\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secf_n_be\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, u256_sub_be\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecf_reducen_done\n" ++
  ".Lsecf_reducen_copy:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_copy32\n" ++
  "  li a0, 0\n" ++
  ".Lsecf_reducen_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Add two scalars modulo n. Inputs and output are 32-byte BE buffers. -/
def secp256k1ScalarFieldAddFunction : String :=
  "secf_add_mod_n:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la s3, secf_tmp0\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s1\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_add_be\n" ++
  "  mv s4, a0\n" ++
  "  beqz s4, .Lsecf_addn_reduce\n" ++
  "  mv a0, s3\n" ++
  "  la a1, secf_n_c_be\n" ++
  "  mv a2, s3\n" ++
  "  jal ra, u256_add_be\n" ++
  ".Lsecf_addn_reduce:\n" ++
  "  mv a0, s3\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_reduce_once_n\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Multiply two scalars modulo n via the ziskemu `Arith256Mod` accelerator
    (same route as `secf_mul_mod_p`, with the modulus parameter block
    pointing at n instead of p). -/
def secp256k1ScalarFieldMulFunction : String :=
  "secf_mul_mod_n:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a1\n" ++
  "  mv s1, a2\n" ++
  "  la a1, secf_le_a\n" ++
  "  jal ra, secf_be_to_le\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secf_le_b\n" ++
  "  jal ra, secf_be_to_le\n" ++
  "  la t0, secf_arith_params_n\n" ++
  "  .4byte 0x8022a073           # csrs 0x802, t0 -> Arith256Mod\n" ++
  "  la a0, secf_le_d\n" ++
  "  mv a1, s1\n" ++
  "  jal ra, secf_le_to_be\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-- Square one scalar modulo n. -/
def secp256k1ScalarFieldSquareFunction : String :=
  "secf_square_mod_n:\n" ++
  "  mv a1, a0\n" ++
  "  jal zero, secf_mul_mod_n"

/-- Modular exponentiation modulo n by a 256-bit BE exponent. -/
def secp256k1ScalarFieldPowFunction : String :=
  "secf_pow_mod_n:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp)\n" ++
  "  sd s5, 48(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  mv s2, a2\n" ++
  "  la s4, secf_pow_result\n" ++
  "  la s5, secf_pow_base\n" ++
  "  la a0, secp256k1_one_be\n" ++
  "  mv a1, s4\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s5\n" ++
  "  jal ra, secf_reduce_once_n\n" ++
  "  li s3, 255\n" ++
  ".Lsecf_pown_loop:\n" ++
  "  mv a0, s4\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_square_mod_n\n" ++
  "  mv a0, s1\n" ++
  "  mv a1, s3\n" ++
  "  jal ra, secf_get_bit_lsb\n" ++
  "  beqz a0, .Lsecf_pown_after_mul\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s5\n" ++
  "  mv a2, s4\n" ++
  "  jal ra, secf_mul_mod_n\n" ++
  ".Lsecf_pown_after_mul:\n" ++
  "  beqz s3, .Lsecf_pown_done\n" ++
  "  addi s3, s3, -1\n" ++
  "  j .Lsecf_pown_loop\n" ++
  ".Lsecf_pown_done:\n" ++
  "  mv a0, s4\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_copy32\n" ++
  "  li a0, 0\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp)\n" ++
  "  ld s5, 48(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"

/-- Invert a nonzero scalar modulo n via Fermat (x^(n-2) mod n).
    Returns a0 = 1 for zero input (output zeroed), else 0. -/
def secp256k1ScalarFieldInvFunction : String :=
  "secf_inv_mod_n:\n" ++
  "  addi sp, sp, -64\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  mv s0, a0\n" ++
  "  mv s1, a1\n" ++
  "  jal ra, secf_is_zero32\n" ++
  "  beqz a0, .Lsecf_invn_nonzero\n" ++
  "  mv a0, s1\n" ++
  "  jal ra, secf_zero32\n" ++
  "  li a0, 1\n" ++
  "  j .Lsecf_invn_done\n" ++
  ".Lsecf_invn_nonzero:\n" ++
  "  la a0, secf_n_minus_2_be\n" ++
  "  addi a1, sp, 24\n" ++
  "  jal ra, secf_copy32\n" ++
  "  mv a0, s0\n" ++
  "  addi a1, sp, 24\n" ++
  "  mv a2, s1\n" ++
  "  jal ra, secf_pow_mod_n\n" ++
  "  li a0, 0\n" ++
  ".Lsecf_invn_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  addi sp, sp, 64\n" ++
  "  ret"


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
