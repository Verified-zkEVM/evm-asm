/-
  EvmAsm.Codegen.Programs.Secp256k1Recover

  Codegen-only secp256k1 curve-level R-point recovery for staged software
  public-key recovery (bead evm-asm-mcogi.5.3.4).

  Given a signature `r` value and a recovery id `recid`, decompress the
  curve point `R = (x, y)`:

    * candidate x = r            (recid bit 1 clear), or
                  = r + n        (recid bit 1 set, the high recovery bit),
      rejecting x >= p (status 2);
    * rhs = x^3 + 7 (mod p);
    * y = sqrt(rhs); reject when rhs is a non-residue (status 1);
    * pick the y whose parity matches `recid & 1`, flipping via y = p - y.

  This mirrors execution-specs `secp256k1_recover`'s `is_square` /
  point-decompression check (crypto/elliptic_curve.py) and the
  coincurve recovery contract. No transaction decoding lives here; inputs
  are raw r/recid values. Field arithmetic is reused from
  `Secp256k1Field` (p-field add/sub/mul/square/sqrt and the BE u256
  helpers).

  Calling convention (`secp256k1_recover_r`):
    a0: pointer to 32-byte big-endian `r`
    a1: recovery id (`recid`); bit 0 selects y parity, bit 1 adds n to x
    a2: pointer to a 64-byte output buffer; on success holds x||y as two
        32-byte big-endian field elements
    returns a0 = 0 on success, 1 if rhs is a non-residue (no curve point),
            2 if the candidate x is out of field range.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Secp256k1Field

namespace EvmAsm.Codegen

open EvmAsm.Rv64

/-- Extra data for curve recovery: the group order `n`, the curve constant
    `b = 7`, and scratch cells. Appended to the field data section (same
    `.data` section, so no extra `.section` header is required). -/
def secp256k1RecoverDataSection : String :=
  ".balign 8\n" ++
  "secp256k1_n_be:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "secp256k1_b_be:\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00\n" ++
  "  .byte 0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x07\n" ++
  ".balign 8\n" ++
  "secf_recover_cmp:\n" ++
  "  .zero 8\n" ++
  ".balign 8\n" ++
  "secf_recover_t:\n" ++
  "  .zero 32\n" ++
  ".balign 8\n" ++
  "secf_recover_rhs:\n" ++
  "  .zero 32\n"

/--
  Decompress the curve point `R = (x, y)` from a signature `r` and
  recovery id. See module docstring for the calling convention.
-/
def secp256k1RecoverRFunction : String :=
  "secp256k1_recover_r:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp)\n" ++
  "  sd s1, 16(sp)\n" ++
  "  sd s2, 24(sp)\n" ++
  "  mv s0, a0                 # r pointer\n" ++
  "  mv s1, a1                 # recid\n" ++
  "  mv s2, a2                 # output: x at s2, y at s2+32\n" ++
  "  andi t0, s1, 2\n" ++
  "  beqz t0, .Lrec_x_is_r\n" ++
  "  # candidate x = r + n\n" ++
  "  mv a0, s0\n" ++
  "  la a1, secp256k1_n_be\n" ++
  "  mv a2, s2\n" ++
  "  jal ra, u256_add_be\n" ++
  "  beqz a0, .Lrec_check_range\n" ++
  "  li a0, 2                  # carry: x >= 2^256\n" ++
  "  j .Lrec_done\n" ++
  ".Lrec_check_range:\n" ++
  "  mv a0, s2\n" ++
  "  la a1, secp256k1_p_be\n" ++
  "  la a2, secf_recover_cmp\n" ++
  "  jal ra, u256_lt_be        # [cmp] = 1 iff x < p\n" ++
  "  la t0, secf_recover_cmp\n" ++
  "  ld t1, 0(t0)\n" ++
  "  bnez t1, .Lrec_have_x\n" ++
  "  li a0, 2                  # x >= p\n" ++
  "  j .Lrec_done\n" ++
  ".Lrec_x_is_r:\n" ++
  "  mv a0, s0\n" ++
  "  mv a1, s2\n" ++
  "  jal ra, secf_copy32\n" ++
  ".Lrec_have_x:\n" ++
  "  # rhs = x^3 + 7\n" ++
  "  mv a0, s2\n" ++
  "  la a2, secf_recover_t\n" ++
  "  jal ra, secf_square_mod_p     # t = x^2\n" ++
  "  la a0, secf_recover_t\n" ++
  "  mv a1, s2\n" ++
  "  la a2, secf_recover_t\n" ++
  "  jal ra, secf_mul_mod_p        # t = x^3\n" ++
  "  la a0, secf_recover_t\n" ++
  "  la a1, secp256k1_b_be\n" ++
  "  la a2, secf_recover_rhs\n" ++
  "  jal ra, secf_add_mod_p        # rhs = x^3 + 7\n" ++
  "  # y = sqrt(rhs) into y slot\n" ++
  "  la a0, secf_recover_rhs\n" ++
  "  addi a1, s2, 32\n" ++
  "  jal ra, secf_sqrt_mod_p\n" ++
  "  beqz a0, .Lrec_have_y\n" ++
  "  li a0, 1                  # rhs is not a quadratic residue\n" ++
  "  j .Lrec_done\n" ++
  ".Lrec_have_y:\n" ++
  "  # match parity: desired = recid & 1, current = LSB of y\n" ++
  "  addi t0, s2, 32\n" ++
  "  lbu t1, 31(t0)            # least-significant byte of y\n" ++
  "  andi t1, t1, 1\n" ++
  "  andi t2, s1, 1\n" ++
  "  beq t1, t2, .Lrec_ok\n" ++
  "  # flip parity: y = p - y\n" ++
  "  la a0, secp256k1_p_be\n" ++
  "  addi a1, s2, 32\n" ++
  "  addi a2, s2, 32\n" ++
  "  jal ra, u256_sub_be\n" ++
  ".Lrec_ok:\n" ++
  "  li a0, 0\n" ++
  ".Lrec_done:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp)\n" ++
  "  ld s1, 16(sp)\n" ++
  "  ld s2, 24(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

/-- Probe prologue: read `r` (0x40000008) and `recid` (0x40000028) from the
    ziskemu input region, call recovery, and write status + x||y to the
    output region (status at 0xa0010000, x||y at 0xa0010008). -/
def ziskSecp256k1RecoverRPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li a3, 0x40000000\n" ++
  "  addi a0, a3, 8\n" ++
  "  ld a1, 40(a3)\n" ++
  "  li a2, 0xa0010008\n" ++
  "  jal ra, secp256k1_recover_r\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Lsecp_recover_probe_done\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  secp256k1FieldCommonFunctions ++ "\n" ++
  ".Lsecp_recover_probe_done:"

def ziskSecp256k1RecoverRProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskSecp256k1RecoverRPrologue
  dataAsm     := secp256k1FieldDataSection ++ secp256k1RecoverDataSection
}

end EvmAsm.Codegen
