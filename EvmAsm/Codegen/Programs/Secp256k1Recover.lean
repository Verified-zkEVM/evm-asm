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
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
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
def secp256k1RecoverR_prog : Program :=
  [ .ADDI .x2 .x2 (-48 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x8 (8 : BitVec 12),
    .SD .x2 .x9 (16 : BitVec 12),
    .SD .x2 .x18 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .ANDI .x5 .x9 (2 : BitVec 12),
    .BEQ .x5 .x0 (84 : BitVec 13),
    .MV .x10 .x8,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_n_be (GuestAddrs.secp256k1_recover_r + 44)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_n_be (GuestAddrs.secp256k1_recover_r + 44)),
    .MV .x12 .x18,
    .JAL .x1 (jalOff GuestAddrs.u256_add_be (GuestAddrs.secp256k1_recover_r + 56)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (204 : BitVec 21),
    .MV .x10 .x18,
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secp256k1_recover_r + 76)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secp256k1_recover_r + 76)),
    .AUIPC .x12 (laHi GuestAddrs.secf_recover_cmp (GuestAddrs.secp256k1_recover_r + 84)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_recover_cmp (GuestAddrs.secp256k1_recover_r + 84)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.secp256k1_recover_r + 92)),
    .AUIPC .x5 (laHi GuestAddrs.secf_recover_cmp (GuestAddrs.secp256k1_recover_r + 96)),
    .ADDI .x5 .x5 (laLo GuestAddrs.secf_recover_cmp (GuestAddrs.secp256k1_recover_r + 96)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (24 : BitVec 13),
    .LI .x10 (2 : Word),
    .JAL .x0 (156 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x18,
    .JAL .x1 (jalOff GuestAddrs.secf_copy32 (GuestAddrs.secp256k1_recover_r + 128)),
    .MV .x10 .x18,
    .AUIPC .x12 (laHi GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 136)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 136)),
    .JAL .x1 (jalOff GuestAddrs.secf_square_mod_p (GuestAddrs.secp256k1_recover_r + 144)),
    .AUIPC .x10 (laHi GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 148)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 148)),
    .MV .x11 .x18,
    .AUIPC .x12 (laHi GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 160)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 160)),
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_p (GuestAddrs.secp256k1_recover_r + 168)),
    .AUIPC .x10 (laHi GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 172)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_recover_t (GuestAddrs.secp256k1_recover_r + 172)),
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_b_be (GuestAddrs.secp256k1_recover_r + 180)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_b_be (GuestAddrs.secp256k1_recover_r + 180)),
    .AUIPC .x12 (laHi GuestAddrs.secf_recover_rhs (GuestAddrs.secp256k1_recover_r + 188)),
    .ADDI .x12 .x12 (laLo GuestAddrs.secf_recover_rhs (GuestAddrs.secp256k1_recover_r + 188)),
    .JAL .x1 (jalOff GuestAddrs.secf_add_mod_p (GuestAddrs.secp256k1_recover_r + 196)),
    .AUIPC .x10 (laHi GuestAddrs.secf_recover_rhs (GuestAddrs.secp256k1_recover_r + 200)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_recover_rhs (GuestAddrs.secp256k1_recover_r + 200)),
    .ADDI .x11 .x18 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.secf_sqrt_mod_p (GuestAddrs.secp256k1_recover_r + 212)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (1 : Word),
    .JAL .x0 (48 : BitVec 21),
    .ADDI .x5 .x18 (32 : BitVec 12),
    .LBU .x6 .x5 (31 : BitVec 12),
    .ANDI .x6 .x6 (1 : BitVec 12),
    .ANDI .x7 .x9 (1 : BitVec 12),
    .BEQ .x6 .x7 (24 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.secp256k1_p_be (GuestAddrs.secp256k1_recover_r + 248)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secp256k1_p_be (GuestAddrs.secp256k1_recover_r + 248)),
    .ADDI .x11 .x18 (32 : BitVec 12),
    .ADDI .x12 .x18 (32 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secp256k1_recover_r + 264)),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secp256k1RecoverR_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secp256k1RecoverR_relocs : RelocTable :=
  [ (11, .la .x11 "secp256k1_n_be"),
    (14, .jal .x1 "u256_add_be"),
    (19, .la .x11 "secp256k1_p_be"),
    (21, .la .x12 "secf_recover_cmp"),
    (23, .jal .x1 "u256_lt_be"),
    (24, .la .x5 "secf_recover_cmp"),
    (32, .jal .x1 "secf_copy32"),
    (34, .la .x12 "secf_recover_t"),
    (36, .jal .x1 "secf_square_mod_p"),
    (37, .la .x10 "secf_recover_t"),
    (40, .la .x12 "secf_recover_t"),
    (42, .jal .x1 "secf_mul_mod_p"),
    (43, .la .x10 "secf_recover_t"),
    (45, .la .x11 "secp256k1_b_be"),
    (47, .la .x12 "secf_recover_rhs"),
    (49, .jal .x1 "secf_add_mod_p"),
    (50, .la .x10 "secf_recover_rhs"),
    (53, .jal .x1 "secf_sqrt_mod_p"),
    (62, .la .x10 "secp256k1_p_be"),
    (66, .jal .x1 "u256_sub_be") ]

def secp256k1RecoverRFunction : String :=
  "secp256k1_recover_r:\n" ++ emitProgramR secp256k1RecoverR_prog secp256k1RecoverR_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secp256k1RecoverR_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1RecoverRFunction_eq_prog :
    secp256k1RecoverRFunction = "secp256k1_recover_r:\n" ++ emitProgramR secp256k1RecoverR_prog secp256k1RecoverR_relocs := rfl

#guard secp256k1RecoverRFunction.startsWith "secp256k1_recover_r:\n"
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


end EvmAsm.Codegen
