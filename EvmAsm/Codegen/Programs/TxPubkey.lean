/-
  EvmAsm.Codegen.Programs.TxPubkey

  Transaction public-key verification substrate. This slice routes one
  transaction to the right signature extractor and signing-hash builder; the
  following slice uses the produced material for secp256k1 recovery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Emit
import EvmAsm.Codegen.GuestAddrs
import EvmAsm.Codegen.AsmReloc
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.U256
import EvmAsm.Codegen.Programs.Secp256k1Field
import EvmAsm.Codegen.Programs.Secp256k1Curve
import EvmAsm.Codegen.Programs.Secp256k1Recover

namespace EvmAsm.Codegen

open EvmAsm.Rv64
open EvmAsm.Rv64.Program

/-! ## tx_pubkey_signature_material

    Build the canonical signature material needed to verify an Amsterdam
    `stateless_input.public_keys[i]` entry against the i-th transaction.
    Mirrors execution-specs Amsterdam `recover_transaction_public_key` up to,
    but not including, the secp256k1 recovery call:

      (r, s, recovery_id, signing_hash) =
        _signature_recovery_parameters(chain_id, tx)

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : output ptr
      ra (input)  : return
      a0 (output) : status

    Output layout at `a3`:
      +0   tx type (0 legacy, 1 EIP-2930, 2 EIP-1559, 3 EIP-4844, 4 EIP-7702)
      +8   recovery id / y_parity (0 or 1)
      +16  r, 32-byte BE
      +48  s, 32-byte BE
      +80  signing hash, 32 bytes
      +112 inner offset
      +120 legacy is_eip155 flag

    Status:
      0 success
      1 tx type dispatch failed
      2 inner offset exceeds tx length
      10 signature extraction failed
      20 signing hash failed
      30 bad legacy v / chain-id mismatch
      31 bad typed y_parity
      40 r is zero
      41 s is zero
      42 r >= SECP256K1N
      43 s > SECP256K1N / 2
-/
def txPubkeySignatureMaterial_prog : Program :=
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
    .SD .x2 .x24 (72 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .MV .x18 .x12,
    .MV .x19 .x13,
    .SD .x19 .x0 (0 : BitVec 12),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (16 : BitVec 12),
    .SD .x19 .x0 (24 : BitVec 12),
    .SD .x19 .x0 (32 : BitVec 12),
    .SD .x19 .x0 (40 : BitVec 12),
    .SD .x19 .x0 (48 : BitVec 12),
    .SD .x19 .x0 (56 : BitVec 12),
    .SD .x19 .x0 (64 : BitVec 12),
    .SD .x19 .x0 (72 : BitVec 12),
    .SD .x19 .x0 (80 : BitVec 12),
    .SD .x19 .x0 (88 : BitVec 12),
    .SD .x19 .x0 (96 : BitVec 12),
    .SD .x19 .x0 (104 : BitVec 12),
    .SD .x19 .x0 (112 : BitVec 12),
    .SD .x19 .x0 (120 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tps_type (GuestAddrs.tx_pubkey_signature_material + 132)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tps_type (GuestAddrs.tx_pubkey_signature_material + 132)),
    .AUIPC .x13 (laHi GuestAddrs.tps_inner_off (GuestAddrs.tx_pubkey_signature_material + 140)),
    .ADDI .x13 .x13 (laLo GuestAddrs.tps_inner_off (GuestAddrs.tx_pubkey_signature_material + 140)),
    .JAL .x1 (jalOff GuestAddrs.tx_type_dispatch (GuestAddrs.tx_pubkey_signature_material + 148)),
    .BNE .x10 .x0 (704 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tps_type (GuestAddrs.tx_pubkey_signature_material + 156)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tps_type (GuestAddrs.tx_pubkey_signature_material + 156)),
    .LD .x20 .x5 (0 : BitVec 12),
    .SD .x19 .x20 (0 : BitVec 12),
    .AUIPC .x5 (laHi GuestAddrs.tps_inner_off (GuestAddrs.tx_pubkey_signature_material + 172)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tps_inner_off (GuestAddrs.tx_pubkey_signature_material + 172)),
    .LD .x21 .x5 (0 : BitVec 12),
    .SD .x19 .x21 (112 : BitVec 12),
    .BLTU .x9 .x21 (676 : BitVec 13),
    .ADD .x22 .x8 .x21,
    .SUB .x23 .x9 .x21,
    .BEQ .x20 .x0 (40 : BitVec 13),
    .LI .x5 (1 : Word),
    .BEQ .x20 .x5 (284 : BitVec 13),
    .LI .x5 (2 : Word),
    .BEQ .x20 .x5 (336 : BitVec 13),
    .LI .x5 (3 : Word),
    .BEQ .x20 .x5 (388 : BitVec 13),
    .LI .x5 (4 : Word),
    .BEQ .x20 .x5 (440 : BitVec 13),
    .JAL .x0 (620 : BitVec 21),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .AUIPC .x12 (laHi GuestAddrs.tps_v (GuestAddrs.tx_pubkey_signature_material + 248)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tps_v (GuestAddrs.tx_pubkey_signature_material + 248)),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_legacy_extract_signature (GuestAddrs.tx_pubkey_signature_material + 264)),
    .BNE .x10 .x0 (604 : BitVec 13),
    .AUIPC .x5 (laHi GuestAddrs.tps_v (GuestAddrs.tx_pubkey_signature_material + 272)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tps_v (GuestAddrs.tx_pubkey_signature_material + 272)),
    .LD .x6 .x5 (0 : BitVec 12),
    .LI .x7 (27 : Word),
    .BEQ .x6 .x7 (40 : BitVec 13),
    .LI .x7 (28 : Word),
    .BEQ .x6 .x7 (72 : BitVec 13),
    .SLLI .x7 .x18 (1 : BitVec 6),
    .LI .x28 (35 : Word),
    .ADD .x28 .x28 .x7,
    .BEQ .x6 .x28 (100 : BitVec 13),
    .ADDI .x28 .x28 (1 : BitVec 12),
    .BEQ .x6 .x28 (132 : BitVec 13),
    .JAL .x0 (564 : BitVec 21),
    .SD .x19 .x0 (8 : BitVec 12),
    .SD .x19 .x0 (120 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (6 : Word),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 356)),
    .BNE .x10 .x0 (520 : BitVec 13),
    .JAL .x0 (380 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (8 : BitVec 12),
    .SD .x19 .x0 (120 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .LI .x12 (6 : Word),
    .LI .x13 (0 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 400)),
    .BNE .x10 .x0 (476 : BitVec 13),
    .JAL .x0 (336 : BitVec 21),
    .SD .x19 .x0 (8 : BitVec 12),
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (120 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .ADDI .x13 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash_legacy_eip155 (GuestAddrs.tx_pubkey_signature_material + 440)),
    .BNE .x10 .x0 (436 : BitVec 13),
    .JAL .x0 (296 : BitVec 21),
    .LI .x5 (1 : Word),
    .SD .x19 .x5 (8 : BitVec 12),
    .SD .x19 .x5 (120 : BitVec 12),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .ADDI .x13 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash_legacy_eip155 (GuestAddrs.tx_pubkey_signature_material + 480)),
    .BNE .x10 .x0 (396 : BitVec 13),
    .JAL .x0 (256 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x19 (8 : BitVec 12),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_eip2930_extract_signature (GuestAddrs.tx_pubkey_signature_material + 512)),
    .BNE .x10 .x0 (356 : BitVec 13),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .LI .x12 (8 : Word),
    .LI .x13 (1 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 540)),
    .BNE .x10 .x0 (336 : BitVec 13),
    .JAL .x0 (184 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x19 (8 : BitVec 12),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_eip1559_extract_signature (GuestAddrs.tx_pubkey_signature_material + 572)),
    .BNE .x10 .x0 (296 : BitVec 13),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .LI .x12 (9 : Word),
    .LI .x13 (2 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 600)),
    .BNE .x10 .x0 (276 : BitVec 13),
    .JAL .x0 (124 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x19 (8 : BitVec 12),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_eip4844_extract_signature (GuestAddrs.tx_pubkey_signature_material + 632)),
    .BNE .x10 .x0 (236 : BitVec 13),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .LI .x12 (11 : Word),
    .LI .x13 (3 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 660)),
    .BNE .x10 .x0 (216 : BitVec 13),
    .JAL .x0 (64 : BitVec 21),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .ADDI .x12 .x19 (8 : BitVec 12),
    .ADDI .x13 .x19 (16 : BitVec 12),
    .ADDI .x14 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_eip7702_extract_signature (GuestAddrs.tx_pubkey_signature_material + 692)),
    .BNE .x10 .x0 (176 : BitVec 13),
    .MV .x10 .x22,
    .MV .x11 .x23,
    .LI .x12 (10 : Word),
    .LI .x13 (4 : Word),
    .ADDI .x14 .x19 (80 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_signing_hash (GuestAddrs.tx_pubkey_signature_material + 720)),
    .BNE .x10 .x0 (156 : BitVec 13),
    .JAL .x0 (4 : BitVec 21),
    .LD .x5 .x19 (8 : BitVec 12),
    .LI .x6 (1 : Word),
    .BLTU .x6 .x5 (156 : BitVec 13),
    .ADDI .x10 .x19 (16 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.tx_pubkey_signature_material + 748)),
    .BNE .x10 .x0 (152 : BitVec 13),
    .ADDI .x10 .x19 (48 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.u256_is_zero (GuestAddrs.tx_pubkey_signature_material + 760)),
    .BNE .x10 .x0 (148 : BitVec 13),
    .ADDI .x10 .x19 (16 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tps_secp256k1_n (GuestAddrs.tx_pubkey_signature_material + 772)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tps_secp256k1_n (GuestAddrs.tx_pubkey_signature_material + 772)),
    .AUIPC .x12 (laHi GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 780)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 780)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.tx_pubkey_signature_material + 788)),
    .AUIPC .x5 (laHi GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 792)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 792)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BEQ .x6 .x0 (116 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.tps_secp256k1_half_n (GuestAddrs.tx_pubkey_signature_material + 808)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tps_secp256k1_half_n (GuestAddrs.tx_pubkey_signature_material + 808)),
    .ADDI .x11 .x19 (48 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 820)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 820)),
    .JAL .x1 (jalOff GuestAddrs.u256_lt_be (GuestAddrs.tx_pubkey_signature_material + 828)),
    .AUIPC .x5 (laHi GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 832)),
    .ADDI .x5 .x5 (laLo GuestAddrs.tps_cmp (GuestAddrs.tx_pubkey_signature_material + 832)),
    .LD .x6 .x5 (0 : BitVec 12),
    .BNE .x6 .x0 (84 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (80 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (72 : BitVec 21),
    .LI .x10 (2 : Word),
    .JAL .x0 (64 : BitVec 21),
    .LI .x10 (10 : Word),
    .JAL .x0 (56 : BitVec 21),
    .LI .x10 (20 : Word),
    .JAL .x0 (48 : BitVec 21),
    .LI .x10 (30 : Word),
    .JAL .x0 (40 : BitVec 21),
    .LI .x10 (31 : Word),
    .JAL .x0 (32 : BitVec 21),
    .LI .x10 (40 : Word),
    .JAL .x0 (24 : BitVec 21),
    .LI .x10 (41 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (42 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (43 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .LD .x22 .x2 (56 : BitVec 12),
    .LD .x23 .x2 (64 : BitVec 12),
    .LD .x24 .x2 (72 : BitVec 12),
    .ADDI .x2 .x2 (80 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txPubkeySignatureMaterial_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txPubkeySignatureMaterial_relocs : RelocTable :=
  [ (33, .la .x12 "tps_type"),
    (35, .la .x13 "tps_inner_off"),
    (37, .jal .x1 "tx_type_dispatch"),
    (39, .la .x5 "tps_type"),
    (43, .la .x5 "tps_inner_off"),
    (62, .la .x12 "tps_v"),
    (66, .jal .x1 "tx_legacy_extract_signature"),
    (68, .la .x5 "tps_v"),
    (89, .jal .x1 "tx_signing_hash"),
    (100, .jal .x1 "tx_signing_hash"),
    (110, .jal .x1 "tx_signing_hash_legacy_eip155"),
    (120, .jal .x1 "tx_signing_hash_legacy_eip155"),
    (128, .jal .x1 "tx_eip2930_extract_signature"),
    (135, .jal .x1 "tx_signing_hash"),
    (143, .jal .x1 "tx_eip1559_extract_signature"),
    (150, .jal .x1 "tx_signing_hash"),
    (158, .jal .x1 "tx_eip4844_extract_signature"),
    (165, .jal .x1 "tx_signing_hash"),
    (173, .jal .x1 "tx_eip7702_extract_signature"),
    (180, .jal .x1 "tx_signing_hash"),
    (187, .jal .x1 "u256_is_zero"),
    (190, .jal .x1 "u256_is_zero"),
    (193, .la .x11 "tps_secp256k1_n"),
    (195, .la .x12 "tps_cmp"),
    (197, .jal .x1 "u256_lt_be"),
    (198, .la .x5 "tps_cmp"),
    (202, .la .x10 "tps_secp256k1_half_n"),
    (205, .la .x12 "tps_cmp"),
    (207, .jal .x1 "u256_lt_be"),
    (208, .la .x5 "tps_cmp") ]

def txPubkeySignatureMaterialFunction : String :=
  "tx_pubkey_signature_material:\n" ++ emitProgramR txPubkeySignatureMaterial_prog txPubkeySignatureMaterial_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txPubkeySignatureMaterial_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txPubkeySignatureMaterialFunction_eq_prog :
    txPubkeySignatureMaterialFunction = "tx_pubkey_signature_material:\n" ++ emitProgramR txPubkeySignatureMaterial_prog txPubkeySignatureMaterial_relocs := rfl

#guard txPubkeySignatureMaterialFunction.startsWith "tx_pubkey_signature_material:\n"
#guard txPubkeySignatureMaterial_prog.length = 245
/-! ## tx_pubkey_ecrecover_stage_material

    Stage `tx_pubkey_signature_material` output into the byte layout consumed by
    `zkvm_secp256k1_ecrecover(msg, sig, recid, output)`.

    Calling convention:
      a0 (input)  : material ptr from `tx_pubkey_signature_material`
      a1 (input)  : output/staging ptr
      ra (input)  : return
      a0 (output) : status

    Staging output at `a1`:
      +0    32-byte message hash
      +32   64-byte signature (`r || s`)
      +96   recid as u64 word (low byte consumed by backend)
      +104  reserved 64-byte recovered-pubkey buffer, pre-zeroed

    Status:
      0 success
      1 recid outside {0, 1}

    Scalar and signing-hash validity are owned by `tx_pubkey_signature_material`;
    this helper is deliberately just the ABI staging layer for the later recovery
    and compare slices. -/
def txPubkeyEcrecoverStageMaterial_prog : Program :=
  [ .ADDI .x2 .x2 (-32 : BitVec 12),
    .SD .x2 .x8 (0 : BitVec 12),
    .SD .x2 .x9 (8 : BitVec 12),
    .SD .x2 .x18 (16 : BitVec 12),
    .SD .x2 .x19 (24 : BitVec 12),
    .MV .x8 .x10,
    .MV .x9 .x11,
    .LD .x18 .x8 (8 : BitVec 12),
    .LI .x5 (1 : Word),
    .BLTU .x5 .x18 (112 : BitVec 13),
    .ADDI .x5 .x8 (80 : BitVec 12),
    .MV .x6 .x9,
    .LI .x7 (4 : Word),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .ADDI .x5 .x8 (16 : BitVec 12),
    .ADDI .x6 .x9 (32 : BitVec 12),
    .LI .x7 (8 : Word),
    .LD .x28 .x5 (0 : BitVec 12),
    .SD .x6 .x28 (0 : BitVec 12),
    .ADDI .x5 .x5 (8 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-20 : BitVec 13),
    .SD .x9 .x18 (96 : BitVec 12),
    .ADDI .x6 .x9 (104 : BitVec 12),
    .LI .x7 (8 : Word),
    .SD .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (1 : Word),
    .LD .x8 .x2 (0 : BitVec 12),
    .LD .x9 .x2 (8 : BitVec 12),
    .LD .x18 .x2 (16 : BitVec 12),
    .LD .x19 .x2 (24 : BitVec 12),
    .ADDI .x2 .x2 (32 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

def txPubkeyEcrecoverStageMaterialFunction : String :=
  "tx_pubkey_ecrecover_stage_material:\n" ++ emitProgram txPubkeyEcrecoverStageMaterial_prog

/-- Kernel-checked drift guard: the Codegen helper string is exactly
    `txPubkeyEcrecoverStageMaterial_prog` rendered under its label (bead evm-asm-4ch8f.9,
    mechanical conversion by `scripts/asm_to_program.py`; guest binary
    byte-identity verified offline by assemble+cmp of the `.text`). -/
theorem txPubkeyEcrecoverStageMaterialFunction_eq_prog :
    txPubkeyEcrecoverStageMaterialFunction = "tx_pubkey_ecrecover_stage_material:\n" ++ emitProgram txPubkeyEcrecoverStageMaterial_prog := rfl

#guard txPubkeyEcrecoverStageMaterialFunction.startsWith "tx_pubkey_ecrecover_stage_material:\n"
#guard txPubkeyEcrecoverStageMaterial_prog.length = 44
/-! ## tx_pubkey_recover_raw

    Callable recovered-key helper surface. Mirrors execution-specs Amsterdam
    `recover_transaction_public_key`: build the signature material, stage it into
    the `zkvm_secp256k1_ecrecover(msg, sig, recid, output)` ABI, then run software
    secp256k1 recovery to produce the 64-byte public key. The safe-fail
    accelerator wrapper is deliberately NOT used, and no stateless `public_keys`
    comparison happens here.

    Recovery math (standard ECDSA, matching execution-specs `secp256k1_recover`):
      e      = msg_hash mod n
      r_inv  = r^{-1} mod n
      u1     = (-e * r_inv) mod n
      u2     = ( s * r_inv) mod n
      R      = curve point decompressed from r and the recovery id
      Q      = u1 * G + u2 * R
    and Q's affine x||y is the recovered public key. Composes the
    `Secp256k1Field` mod-n scalar helpers (reduce/mul/inv), the `Secp256k1Recover`
    R-decompression, and the `Secp256k1Curve` scalar-mul / point-add primitives.

    PERFORMANCE: the field multiplies and affine point operations are backed
    by the ziskemu accelerators (`Arith256Mod` / `Secp256k1Add` /
    `Secp256k1Dbl`, see `Secp256k1Field` / `Secp256k1Curve`), so one full
    recovery is ~2e6 ziskemu steps -- comfortably inside the stateless guest's
    ~1e9 step budget (the earlier all-software stack was ~1e11 steps).

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : recovered-pubkey output ptr (64 bytes, BE x || y)
      a4 (input)  : scratch ptr (>= 304 bytes, 8-byte aligned)
      ra (input)  : return
      a0 (output) : status

    Scratch layout at `a4`:
      +0    material status side slot (u64; meaningful when status == 10)
      +8    signature material block (128 bytes; `tx_pubkey_signature_material`
            output: type/recid/r/s/hash/inner_off/is_eip155)
      +136  staged ecrecover ABI block (168 bytes; msg hash 32 @+0 || sig r 32
            @+32 || sig s 32 @+64 || recid word 8 @+96 || reserved pubkey 64)

    Status:
      0  success: recovered public key written to the output buffer
      10 signature material failed (material status stored at scratch +0)
      20 ecrecover ABI staging failed
      60 secp256k1 recovery failed (R is off-curve / out of range, or the
         recovered point is the identity)

    On any nonzero status the recovered-pubkey output buffer is zeroed so callers
    never observe stale or partial coordinates from a failed run. -/
def txPubkeyRecoverRaw_prog : Program :=
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
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .ADDI .x13 .x20 (8 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_pubkey_signature_material (GuestAddrs.tx_pubkey_recover_raw + 64)),
    .SD .x20 .x10 (0 : BitVec 12),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (10 : Word),
    .JAL .x0 (60 : BitVec 21),
    .ADDI .x10 .x20 (8 : BitVec 12),
    .ADDI .x11 .x20 (136 : BitVec 12),
    .JAL .x1 (jalOff GuestAddrs.tx_pubkey_ecrecover_stage_material (GuestAddrs.tx_pubkey_recover_raw + 92)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (20 : Word),
    .JAL .x0 (36 : BitVec 21),
    .ADDI .x10 .x20 (136 : BitVec 12),
    .MV .x11 .x19,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_recover_pubkey_staged (GuestAddrs.tx_pubkey_recover_raw + 116)),
    .BEQ .x10 .x0 (12 : BitVec 13),
    .LI .x10 (60 : Word),
    .JAL .x0 (12 : BitVec 21),
    .LI .x10 (0 : Word),
    .JAL .x0 (4 : BitVec 21),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .ADDI .x2 .x2 (48 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txPubkeyRecoverRaw_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txPubkeyRecoverRaw_relocs : RelocTable :=
  [ (16, .jal .x1 "tx_pubkey_signature_material"),
    (23, .jal .x1 "tx_pubkey_ecrecover_stage_material"),
    (29, .jal .x1 "secp256k1_recover_pubkey_staged") ]

def txPubkeyRecoverRawFunction : String :=
  "tx_pubkey_recover_raw:\n" ++ emitProgramR txPubkeyRecoverRaw_prog txPubkeyRecoverRaw_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txPubkeyRecoverRaw_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txPubkeyRecoverRawFunction_eq_prog :
    txPubkeyRecoverRawFunction = "tx_pubkey_recover_raw:\n" ++ emitProgramR txPubkeyRecoverRaw_prog txPubkeyRecoverRaw_relocs := rfl

#guard txPubkeyRecoverRawFunction.startsWith "tx_pubkey_recover_raw:\n"
#guard txPubkeyRecoverRaw_prog.length = 43
/-! ## secp256k1_recover_pubkey_staged (.62.2.5)

    ECDSA public-key recovery over a staged ABI block — the shared kernel
    behind transaction-sender recovery (`tx_pubkey_recover_raw`) and the
    ECRECOVER (0x01) precompile backend. Same math and accelerator backing as
    documented on `tx_pubkey_recover_raw` above (~2e6 ziskemu steps).

    Calling convention:
      a0 (input)  : staged ABI block ptr: msg hash 32 @+0 || r 32 @+32 ||
                    s 32 @+64 || recid word (u64, 0/1) @+96. All BE 32-byte
                    scalars; the caller has already validated r, s in (0, n).
      a1 (input)  : recovered-pubkey output ptr (64 bytes, BE x || y)
      ra (input)  : return
      a0 (output) : 0 success; 60 recovery failed (R off-curve / out of range,
                    r non-invertible, or the recovered point is the identity).
                    On failure the 64-byte output is zeroed.

    Uses the `tpr_*` static scratch (recovery is not re-entrant). -/
def secp256k1RecoverPubkeyStaged_prog : Program :=
  [ .ADDI .x2 .x2 (-24 : BitVec 12),
    .SD .x2 .x1 (0 : BitVec 12),
    .SD .x2 .x19 (8 : BitVec 12),
    .SD .x2 .x20 (16 : BitVec 12),
    .MV .x20 .x10,
    .MV .x19 .x11,
    .ADDI .x10 .x20 (32 : BitVec 12),
    .LD .x11 .x20 (96 : BitVec 12),
    .AUIPC .x12 (laHi GuestAddrs.tpr_R (GuestAddrs.secp256k1_recover_pubkey_staged + 32)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_R (GuestAddrs.secp256k1_recover_pubkey_staged + 32)),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_recover_r (GuestAddrs.secp256k1_recover_pubkey_staged + 40)),
    .BNE .x10 .x0 (240 : BitVec 13),
    .MV .x10 .x20,
    .AUIPC .x11 (laHi GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 52)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 52)),
    .JAL .x1 (jalOff GuestAddrs.secf_reduce_once_n (GuestAddrs.secp256k1_recover_pubkey_staged + 60)),
    .ADDI .x10 .x20 (32 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 68)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 68)),
    .JAL .x1 (jalOff GuestAddrs.secf_inv_mod_n (GuestAddrs.secp256k1_recover_pubkey_staged + 76)),
    .BNE .x10 .x0 (204 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 84)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 84)),
    .JAL .x1 (jalOff GuestAddrs.secf_is_zero32 (GuestAddrs.secp256k1_recover_pubkey_staged + 92)),
    .BNE .x10 .x0 (36 : BitVec 13),
    .AUIPC .x10 (laHi GuestAddrs.secf_n_be (GuestAddrs.secp256k1_recover_pubkey_staged + 100)),
    .ADDI .x10 .x10 (laLo GuestAddrs.secf_n_be (GuestAddrs.secp256k1_recover_pubkey_staged + 100)),
    .AUIPC .x11 (laHi GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 108)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_e (GuestAddrs.secp256k1_recover_pubkey_staged + 108)),
    .AUIPC .x12 (laHi GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 116)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 116)),
    .JAL .x1 (jalOff GuestAddrs.u256_sub_be (GuestAddrs.secp256k1_recover_pubkey_staged + 124)),
    .JAL .x0 (16 : BitVec 21),
    .AUIPC .x10 (laHi GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 132)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 132)),
    .JAL .x1 (jalOff GuestAddrs.secf_zero32 (GuestAddrs.secp256k1_recover_pubkey_staged + 140)),
    .AUIPC .x10 (laHi GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 144)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_nege (GuestAddrs.secp256k1_recover_pubkey_staged + 144)),
    .AUIPC .x11 (laHi GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 152)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 152)),
    .AUIPC .x12 (laHi GuestAddrs.tpr_u1 (GuestAddrs.secp256k1_recover_pubkey_staged + 160)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_u1 (GuestAddrs.secp256k1_recover_pubkey_staged + 160)),
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secp256k1_recover_pubkey_staged + 168)),
    .ADDI .x10 .x20 (64 : BitVec 12),
    .AUIPC .x11 (laHi GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 176)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_rinv (GuestAddrs.secp256k1_recover_pubkey_staged + 176)),
    .AUIPC .x12 (laHi GuestAddrs.tpr_u2 (GuestAddrs.secp256k1_recover_pubkey_staged + 184)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_u2 (GuestAddrs.secp256k1_recover_pubkey_staged + 184)),
    .JAL .x1 (jalOff GuestAddrs.secf_mul_mod_n (GuestAddrs.secp256k1_recover_pubkey_staged + 192)),
    .AUIPC .x10 (laHi GuestAddrs.tpr_u1 (GuestAddrs.secp256k1_recover_pubkey_staged + 196)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_u1 (GuestAddrs.secp256k1_recover_pubkey_staged + 196)),
    .AUIPC .x11 (laHi GuestAddrs.secp256k1_generator (GuestAddrs.secp256k1_recover_pubkey_staged + 204)),
    .ADDI .x11 .x11 (laLo GuestAddrs.secp256k1_generator (GuestAddrs.secp256k1_recover_pubkey_staged + 204)),
    .AUIPC .x12 (laHi GuestAddrs.tpr_p1 (GuestAddrs.secp256k1_recover_pubkey_staged + 212)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_p1 (GuestAddrs.secp256k1_recover_pubkey_staged + 212)),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_scalar_mul (GuestAddrs.secp256k1_recover_pubkey_staged + 220)),
    .AUIPC .x10 (laHi GuestAddrs.tpr_u2 (GuestAddrs.secp256k1_recover_pubkey_staged + 224)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_u2 (GuestAddrs.secp256k1_recover_pubkey_staged + 224)),
    .AUIPC .x11 (laHi GuestAddrs.tpr_R (GuestAddrs.secp256k1_recover_pubkey_staged + 232)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_R (GuestAddrs.secp256k1_recover_pubkey_staged + 232)),
    .AUIPC .x12 (laHi GuestAddrs.tpr_p2 (GuestAddrs.secp256k1_recover_pubkey_staged + 240)),
    .ADDI .x12 .x12 (laLo GuestAddrs.tpr_p2 (GuestAddrs.secp256k1_recover_pubkey_staged + 240)),
    .JAL .x1 (jalOff GuestAddrs.secp256k1_scalar_mul (GuestAddrs.secp256k1_recover_pubkey_staged + 248)),
    .AUIPC .x10 (laHi GuestAddrs.tpr_p1 (GuestAddrs.secp256k1_recover_pubkey_staged + 252)),
    .ADDI .x10 .x10 (laLo GuestAddrs.tpr_p1 (GuestAddrs.secp256k1_recover_pubkey_staged + 252)),
    .AUIPC .x11 (laHi GuestAddrs.tpr_p2 (GuestAddrs.secp256k1_recover_pubkey_staged + 260)),
    .ADDI .x11 .x11 (laLo GuestAddrs.tpr_p2 (GuestAddrs.secp256k1_recover_pubkey_staged + 260)),
    .MV .x12 .x19,
    .JAL .x1 (jalOff GuestAddrs.secp256k1_point_add (GuestAddrs.secp256k1_recover_pubkey_staged + 272)),
    .BNE .x10 .x0 (8 : BitVec 13),
    .JAL .x0 (36 : BitVec 21),
    .MV .x6 .x19,
    .LI .x7 (8 : Word),
    .SD .x6 .x0 (0 : BitVec 12),
    .ADDI .x6 .x6 (8 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-12 : BitVec 13),
    .LI .x10 (60 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (0 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x19 .x2 (8 : BitVec 12),
    .LD .x20 .x2 (16 : BitVec 12),
    .ADDI .x2 .x2 (24 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `secp256k1RecoverPubkeyStaged_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def secp256k1RecoverPubkeyStaged_relocs : RelocTable :=
  [ (8, .la .x12 "tpr_R"),
    (10, .jal .x1 "secp256k1_recover_r"),
    (13, .la .x11 "tpr_e"),
    (15, .jal .x1 "secf_reduce_once_n"),
    (17, .la .x11 "tpr_rinv"),
    (19, .jal .x1 "secf_inv_mod_n"),
    (21, .la .x10 "tpr_e"),
    (23, .jal .x1 "secf_is_zero32"),
    (25, .la .x10 "secf_n_be"),
    (27, .la .x11 "tpr_e"),
    (29, .la .x12 "tpr_nege"),
    (31, .jal .x1 "u256_sub_be"),
    (33, .la .x10 "tpr_nege"),
    (35, .jal .x1 "secf_zero32"),
    (36, .la .x10 "tpr_nege"),
    (38, .la .x11 "tpr_rinv"),
    (40, .la .x12 "tpr_u1"),
    (42, .jal .x1 "secf_mul_mod_n"),
    (44, .la .x11 "tpr_rinv"),
    (46, .la .x12 "tpr_u2"),
    (48, .jal .x1 "secf_mul_mod_n"),
    (49, .la .x10 "tpr_u1"),
    (51, .la .x11 "secp256k1_generator"),
    (53, .la .x12 "tpr_p1"),
    (55, .jal .x1 "secp256k1_scalar_mul"),
    (56, .la .x10 "tpr_u2"),
    (58, .la .x11 "tpr_R"),
    (60, .la .x12 "tpr_p2"),
    (62, .jal .x1 "secp256k1_scalar_mul"),
    (63, .la .x10 "tpr_p1"),
    (65, .la .x11 "tpr_p2"),
    (68, .jal .x1 "secp256k1_point_add") ]

def secp256k1RecoverPubkeyStagedFunction : String :=
  "secp256k1_recover_pubkey_staged:\n" ++ emitProgramR secp256k1RecoverPubkeyStaged_prog secp256k1RecoverPubkeyStaged_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `secp256k1RecoverPubkeyStaged_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem secp256k1RecoverPubkeyStagedFunction_eq_prog :
    secp256k1RecoverPubkeyStagedFunction = "secp256k1_recover_pubkey_staged:\n" ++ emitProgramR secp256k1RecoverPubkeyStaged_prog secp256k1RecoverPubkeyStaged_relocs := rfl

#guard secp256k1RecoverPubkeyStagedFunction.startsWith "secp256k1_recover_pubkey_staged:\n"
#guard secp256k1RecoverPubkeyStaged_prog.length = 85
/-- Static scratch buffers for `tx_pubkey_recover_raw`'s recovery math (the
    decompressed R point, the reduced hash and its negation, `r^{-1}`, the two
    scalars, and the two scalar-mul outputs). Recovery is never re-entrant, so a
    single static region is safe and mirrors the other secp256k1 helpers. Must be
    emitted (once) alongside `secp256k1CurveDataSection` /
    `secp256k1RecoverDataSection` in any build unit that links
    `txPubkeyRecoverRawFunction`. -/
def txPubkeyRecoverRawDataSection : String :=
  ".balign 8\n" ++
  "tpr_R:\n  .zero 64\n" ++
  "tpr_e:\n  .zero 32\n" ++
  "tpr_nege:\n  .zero 32\n" ++
  "tpr_rinv:\n  .zero 32\n" ++
  "tpr_u1:\n  .zero 32\n" ++
  "tpr_u2:\n  .zero 32\n" ++
  "tpr_p1:\n  .zero 64\n" ++
  "tpr_p2:\n  .zero 64\n"

/-! ## tx_pubkey_public_key_matches

    Final `public_keys` comparison helper. Mirrors execution-specs Amsterdam
    `transactions.recover_sender_from_public_key`: the supplied stateless
    `public_keys[i]` entry must equal `recover_transaction_public_key(chain_id,
    tx)`. The supplied key is a 65-byte SEC1 uncompressed point (`0x04 || x || y`);
    this helper checks the `0x04` prefix, recovers the canonical key from the
    transaction signature via `tx_pubkey_recover_raw`, and byte-compares the
    supplied 64 coordinate bytes against the recovered `x || y`.

    The prefix is checked BEFORE recovery: a non-`0x04` key can never match a
    valid recovered point, and the early-out keeps the bad-prefix path free of
    the recovery math (~2e6 ziskemu steps), so it can be probed fast.

    Calling convention:
      a0 (input)  : encoded transaction ptr
      a1 (input)  : encoded transaction byte length
      a2 (input)  : execution chain_id (u64)
      a3 (input)  : supplied public key ptr (65 bytes, 0x04 || BE x || BE y)
      a4 (input)  : recovered-pubkey scratch ptr (64 bytes, written by recover_raw)
      a5 (input)  : recover scratch ptr (>= 304 bytes, 8-byte aligned)
      ra (input)  : return
      a0 (output) : status

    Status:
      0   match: prefix ok, recovery ok, supplied coords == recovered x||y
      1   mismatch: prefix 0x04 and recovery ok, but coordinates differ
      2   bad prefix: supplied[0] != 0x04
      10  signature material failed (from tx_pubkey_recover_raw)
      20  ecrecover ABI staging failed (from tx_pubkey_recover_raw)
      60  secp256k1 recovery failed (from tx_pubkey_recover_raw)

    The 0/1/2 comparison statuses are disjoint from the 10/20/60 recovery
    statuses, so a caller can distinguish all four failure classes. -/
def txPubkeyPublicKeyMatches_prog : Program :=
  [ .ADDI .x2 .x2 (-56 : BitVec 12),
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
    .MV .x19 .x13,
    .MV .x20 .x14,
    .MV .x21 .x15,
    .LBU .x5 .x19 (0 : BitVec 12),
    .LI .x6 (4 : Word),
    .BNE .x5 .x6 (88 : BitVec 13),
    .MV .x10 .x8,
    .MV .x11 .x9,
    .MV .x12 .x18,
    .MV .x13 .x20,
    .MV .x14 .x21,
    .JAL .x1 (jalOff GuestAddrs.tx_pubkey_recover_raw (GuestAddrs.tx_pubkey_public_key_matches + 88)),
    .BNE .x10 .x0 (64 : BitVec 13),
    .ADDI .x5 .x19 (1 : BitVec 12),
    .MV .x6 .x20,
    .LI .x7 (64 : Word),
    .LBU .x28 .x5 (0 : BitVec 12),
    .LBU .x29 .x6 (0 : BitVec 12),
    .BNE .x28 .x29 (28 : BitVec 13),
    .ADDI .x5 .x5 (1 : BitVec 12),
    .ADDI .x6 .x6 (1 : BitVec 12),
    .ADDI .x7 .x7 (-1 : BitVec 12),
    .BNE .x7 .x0 (-24 : BitVec 13),
    .LI .x10 (0 : Word),
    .JAL .x0 (16 : BitVec 21),
    .LI .x10 (1 : Word),
    .JAL .x0 (8 : BitVec 21),
    .LI .x10 (2 : Word),
    .LD .x1 .x2 (0 : BitVec 12),
    .LD .x8 .x2 (8 : BitVec 12),
    .LD .x9 .x2 (16 : BitVec 12),
    .LD .x18 .x2 (24 : BitVec 12),
    .LD .x19 .x2 (32 : BitVec 12),
    .LD .x20 .x2 (40 : BitVec 12),
    .LD .x21 .x2 (48 : BitVec 12),
    .ADDI .x2 .x2 (56 : BitVec 12),
    .JALR .x0 .x1 (0 : BitVec 12) ]

/-- Reloc side-table for `txPubkeyPublicKeyMatches_prog`: the `la`/cross-`jal` instruction indices
    kept SYMBOLIC in the emitted image text (`emitProgramR`), while the Program
    above carries the concrete guest-linked immediates for verification. -/
def txPubkeyPublicKeyMatches_relocs : RelocTable :=
  [ (22, .jal .x1 "tx_pubkey_recover_raw") ]

def txPubkeyPublicKeyMatchesFunction : String :=
  "tx_pubkey_public_key_matches:\n" ++ emitProgramR txPubkeyPublicKeyMatches_prog txPubkeyPublicKeyMatches_relocs

/-- Kernel-checked drift guard: the emitted (image-agnostic, symbolic) Codegen
    string is exactly `txPubkeyPublicKeyMatches_prog` rendered under its label with the `la`/`jal`
    relocs kept symbolic (bead evm-asm-4ch8f.9.3, mechanical conversion by
    `scripts/asm_to_program.py`). Guest binary byte-identity + guest-linked
    consistency of the concrete Program verified offline by assemble/link+cmp. -/
theorem txPubkeyPublicKeyMatchesFunction_eq_prog :
    txPubkeyPublicKeyMatchesFunction = "tx_pubkey_public_key_matches:\n" ++ emitProgramR txPubkeyPublicKeyMatches_prog txPubkeyPublicKeyMatches_relocs := rfl

#guard txPubkeyPublicKeyMatchesFunction.startsWith "tx_pubkey_public_key_matches:\n"
#guard txPubkeyPublicKeyMatches_prog.length = 48
/-- `zisk_tx_pubkey_ecrecover_stage_material`: probe BuildUnit.
    Reads the same input as `zisk_tx_pubkey_signature_material`, first builds
    material at OUTPUT+8, then stages accelerator ABI bytes at OUTPUT+136.

    Output layout:
      +0    material status
      +8    128-byte material block
      +136  stage status
      +144  staged message hash
      +176  staged signature r||s
      +240  staged recid word
      +248  reserved pubkey buffer -/
def ziskTxPubkeyEcrecoverStageMaterialPrologue : String :=
  "  li sp, 0xa0050000
  li a5, 0x40000000
  ld a1, 8(a5)                # tx_len
  ld a2, 16(a5)               # chain_id
  addi a0, a5, 24             # tx ptr
  li a3, 0xa0010008           # material out
  jal ra, tx_pubkey_signature_material
  li s0, 0xa0010000
  sd a0, 0(s0)                # material status
  bnez a0, .Ltpes_probe_done
  addi a0, s0, 8              # material ptr
  addi a1, s0, 144            # staged ABI ptr
  jal ra, tx_pubkey_ecrecover_stage_material
  sd a0, 136(s0)              # stage status
  j .Ltpes_probe_done
" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  ".Ltpes_probe_done:"

/-- `zisk_tx_pubkey_signature_material`: probe BuildUnit.
    Input layout:
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..   : encoded transaction

    Output layout:
      bytes  0.. 8 : status
      bytes  8..   : `tx_pubkey_signature_material` output layout. -/
def ziskTxPubkeySignatureMaterialPrologue : String :=
  "  li sp, 0xa0050000
  li a5, 0x40000000
  ld a1, 8(a5)                # tx_len
  ld a2, 16(a5)               # chain_id
  addi a0, a5, 24             # tx ptr
  li a3, 0xa0010008           # material out
  jal ra, tx_pubkey_signature_material
  li t0, 0xa0010000
  sd a0, 0(t0)
  j .Ltps_pdone
" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  u256LtBeFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  ".Ltps_pdone:"

def ziskTxPubkeySignatureMaterialDataSection : String :=
  ".section .data\n" ++
  ".balign 8\n" ++
  "zk3_state:\n  .zero 200\n" ++
  "tps_type:\n  .zero 8\n" ++
  "tps_inner_off:\n  .zero 8\n" ++
  "tps_v:\n  .zero 8\n" ++
  "tps_cmp:\n  .zero 8\n" ++
  "tps_secp256k1_n:\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff
  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe
  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b
  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41
" ++
  "tps_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff
  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff
  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d
  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0
" ++
  "tlxs_offset:\n  .zero 8\n" ++
  "tlxs_length:\n  .zero 8\n" ++
  "txes_offset:\n  .zero 8\n" ++
  "txes_length:\n  .zero 8\n" ++
  "t29es_offset:\n  .zero 8\n" ++
  "t29es_length:\n  .zero 8\n" ++
  "t44es_offset:\n  .zero 8\n" ++
  "t44es_length:\n  .zero 8\n" ++
  "t77es_offset:\n  .zero 8\n" ++
  "t77es_length:\n  .zero 8\n" ++
  "tsh_buf:\n  .zero 131072\n" ++
  "tsh_trunc_len:\n  .zero 8\n" ++
  "rltn_offset_lo:\n  .zero 8\n" ++
  "rltn_length_lo:\n  .zero 8\n" ++
  "rltn_offset_hi:\n  .zero 8\n" ++
  "rltn_length_hi:\n  .zero 8\n" ++
  "rltn_prefix_len:\n  .zero 8\n" ++
  "t155_buf:\n  .zero 131072\n" ++
  "t155_offset_lo:\n  .zero 8\n" ++
  "t155_length_lo:\n  .zero 8\n" ++
  "t155_offset_hi:\n  .zero 8\n" ++
  "t155_length_hi:\n  .zero 8\n" ++
  "t155_chain_be:\n  .zero 8\n" ++
  "t155_chain_enc:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "t155_prefix_len:\n  .zero 8"



/-- `zisk_tx_pubkey_recover_raw_status`: probe BuildUnit.

    Drives `tx_pubkey_recover_raw` over one transaction and exposes both the
    helper status and the material-failure side slot, so a script can assert a
    valid tx reaches status 50 (material+stage succeeded, recovery backend not
    implemented) while a malformed/high-s tx surfaces the material failure
    class (status 10 with the material status preserved).

    Input layout (same as `zisk_tx_pubkey_signature_material`):
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..   : encoded transaction

    Output layout:
      +0  helper status (10 material fail, 20 stage fail, 50 backend stub)
      +8  material status side slot (meaningful when helper status == 10) -/
def ziskTxPubkeyRecoverRawStatusPrologue : String :=
  "  li sp, 0xa0050000
  li a5, 0x40000000
  ld a1, 8(a5)                # tx_len
  ld a2, 16(a5)               # chain_id
  addi a0, a5, 24             # tx ptr
  la a3, tprr_pubkey_out      # recovered pubkey out (64 bytes)
  la a4, tprr_scratch         # scratch (>= 304 bytes)
  jal ra, tx_pubkey_recover_raw
  li t0, 0xa0010000
  sd a0, 0(t0)                # helper status
  la t1, tprr_scratch
  ld t2, 0(t1)
  sd t2, 8(t0)                # material status side slot
  # copy the 64-byte recovered pubkey (x||y) to output+16 for assertions
  la t1, tprr_pubkey_out
  addi t0, t0, 16
  li t2, 8
" ++
  ".Ltprrs_copy_pub:\n" ++
  "  ld t3, 0(t1); sd t3, 0(t0)
  addi t1, t1, 8; addi t0, t0, 8; addi t2, t2, -1
  bnez t2, .Ltprrs_copy_pub
  j .Ltprrs_pdone
" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  -- secp256k1 recovery stack (curve common already provides u256_lt_be/_add_be/
  -- _sub_be, so the standalone u256_lt_be above is dropped to avoid a duplicate
  -- label).
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  ".Ltprrs_pdone:"

def ziskTxPubkeyRecoverRawStatusDataSection : String :=
  ziskTxPubkeySignatureMaterialDataSection ++ "\n" ++
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  "tprr_pubkey_out:\n  .zero 64\n" ++
  "tprr_scratch:\n  .zero 312"


/-- `zisk_tx_pubkey_public_key_matches_status`: probe BuildUnit.

    Drives `tx_pubkey_public_key_matches` over one transaction and a supplied
    SEC1 public key. The cheap cases (bad prefix; signature-material failure)
    are decided before the recovery, so they run in a small step budget; the
    match/mismatch cases run a full accelerator-backed recovery (~2e6 steps,
    gated behind the check script's `RECOVER_RAW_FULL=1` switch).

    Input layout:
      bytes  0.. 8 : tx byte length
      bytes  8..16 : execution chain_id
      bytes 16..81 : supplied public key (65 bytes, 0x04 || x || y)
      bytes 88..   : encoded transaction (8-byte aligned)

    Output layout:
      +0  match status (0 match, 1 mismatch, 2 bad prefix, 10/20/60 recovery)
      +8  reserved (zero)
      +16 recovered public key (64 bytes, BE x||y; zeroed on recovery failure) -/
def ziskTxPubkeyPublicKeyMatchesStatusPrologue : String :=
  "  li sp, 0xa0050000\n" ++
  "  li t6, 0x40000000           # input base (ziskemu writes an 8-byte length\n" ++
  "                              # header at +0, so user byte k is at t6+8+k)\n" ++
  "  ld a1, 8(t6)                # tx_len      (user +0)
  ld a2, 16(t6)               # chain_id    (user +8)
  addi a3, t6, 24             # supplied public key ptr (65 bytes; user +16)
  addi a0, t6, 96             # tx ptr       (user +88)
  la a4, tpm_pubkey_out       # recovered pubkey out (64 bytes)
  la a5, tpm_scratch          # recover scratch (>= 304 bytes)
  jal ra, tx_pubkey_public_key_matches
  li t0, 0xa0010000
  sd a0, 0(t0)                # match status
  sd zero, 8(t0)              # reserved
  # copy the 64-byte recovered pubkey (x||y) to output+16 for assertions
  la t1, tpm_pubkey_out
  addi t0, t0, 16
  li t2, 8
" ++
  ".Ltpms_copy_pub:\n" ++
  "  ld t3, 0(t1); sd t3, 0(t0)
  addi t1, t1, 8; addi t0, t0, 8; addi t2, t2, -1
  bnez t2, .Ltpms_copy_pub
  j .Ltpms_pdone
" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpWalkHelpersClosure ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
  zkvmKeccak256SegmentsFunction ++ "\n" ++
  u256IsZeroFunction ++ "\n" ++
  -- secp256k1 recovery stack (curve common already provides u256_lt_be/_add_be/
  -- _sub_be, so no standalone u256_lt_be is linked here to avoid a duplicate
  -- label).
  secp256k1CurveCommonFunctions ++ "\n" ++
  secp256k1RecoverRFunction ++ "\n" ++
  txLegacyExtractSignatureFunction ++ "\n" ++
  txEip2930ExtractSignatureFunction ++ "\n" ++
  txEip1559ExtractSignatureFunction ++ "\n" ++
  txEip4844ExtractSignatureFunction ++ "\n" ++
  txEip7702ExtractSignatureFunction ++ "\n" ++
  txSigningHashFunction ++ "\n" ++
  txSigningHashLegacyEip155Function ++ "\n" ++
  txPubkeySignatureMaterialFunction ++ "\n" ++
  txPubkeyEcrecoverStageMaterialFunction ++ "\n" ++
  txPubkeyRecoverRawFunction ++ "\n" ++
  secp256k1RecoverPubkeyStagedFunction ++ "\n" ++
  txPubkeyPublicKeyMatchesFunction ++ "\n" ++
  ".Ltpms_pdone:"

def ziskTxPubkeyPublicKeyMatchesStatusDataSection : String :=
  ziskTxPubkeySignatureMaterialDataSection ++ "\n" ++
  secp256k1CurveDataSection ++ "\n" ++
  secp256k1RecoverDataSection ++ "\n" ++
  txPubkeyRecoverRawDataSection ++ "\n" ++
  "tpm_pubkey_out:\n  .zero 64\n" ++
  "tpm_scratch:\n  .zero 312"


end EvmAsm.Codegen
