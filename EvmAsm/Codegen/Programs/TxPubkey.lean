/-
  EvmAsm.Codegen.Programs.TxPubkey

  Transaction public-key verification substrate. This slice routes one
  transaction to the right signature extractor and signing-hash builder; the
  following slice uses the produced material for secp256k1 recovery.
-/

import EvmAsm.Rv64.Program
import EvmAsm.Codegen.Layout
import EvmAsm.Codegen.Programs.Tx
import EvmAsm.Codegen.Programs.TxExtract
import EvmAsm.Codegen.Programs.TxSignature
import EvmAsm.Codegen.Programs.TxSigningHash
import EvmAsm.Codegen.Programs.U256

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
def txPubkeySignatureMaterialFunction : String :=
  "tx_pubkey_signature_material:\n" ++
  "  addi sp, sp, -80\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp)\n" ++
  "  sd s4, 40(sp); sd s5, 48(sp); sd s6, 56(sp); sd s7, 64(sp); sd s8, 72(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # output ptr\n" ++
  "  sd zero,   0(s3); sd zero,   8(s3); sd zero,  16(s3); sd zero,  24(s3)\n" ++
  "  sd zero,  32(s3); sd zero,  40(s3); sd zero,  48(s3); sd zero,  56(s3)\n" ++
  "  sd zero,  64(s3); sd zero,  72(s3); sd zero,  80(s3); sd zero,  88(s3)\n" ++
  "  sd zero,  96(s3); sd zero, 104(s3); sd zero, 112(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tps_type; la a3, tps_inner_off\n" ++
  "  jal ra, tx_type_dispatch\n" ++
  "  bnez a0, .Ltps_type_fail\n" ++
  "  la t0, tps_type; ld s4, 0(t0); sd s4, 0(s3)\n" ++
  "  la t0, tps_inner_off; ld s5, 0(t0); sd s5, 112(s3)\n" ++
  "  bltu s1, s5, .Ltps_inner_oob\n" ++
  "  add s6, s0, s5              # inner ptr\n" ++
  "  sub s7, s1, s5              # inner len\n" ++
  "  beqz s4, .Ltps_legacy\n" ++
  "  li t0, 1; beq s4, t0, .Ltps_t1\n" ++
  "  li t0, 2; beq s4, t0, .Ltps_t2\n" ++
  "  li t0, 3; beq s4, t0, .Ltps_t3\n" ++
  "  li t0, 4; beq s4, t0, .Ltps_t4\n" ++
  "  j .Ltps_type_fail\n" ++
  ".Ltps_legacy:\n" ++
  "  mv a0, s0; mv a1, s1; la a2, tps_v; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_legacy_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  la t0, tps_v; ld t1, 0(t0)\n" ++
  "  li t2, 27; beq t1, t2, .Ltps_legacy_v27\n" ++
  "  li t2, 28; beq t1, t2, .Ltps_legacy_v28\n" ++
  "  slli t2, s2, 1\n" ++
  "  li t3, 35; add t3, t3, t2\n" ++
  "  beq t1, t3, .Ltps_legacy_eip155_y0\n" ++
  "  addi t3, t3, 1\n" ++
  "  beq t1, t3, .Ltps_legacy_eip155_y1\n" ++
  "  j .Ltps_bad_v\n" ++
  ".Ltps_legacy_v27:\n" ++
  "  sd zero, 8(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_v28:\n" ++
  "  li t0, 1; sd t0, 8(s3); sd zero, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; li a2, 6; li a3, 0; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_eip155_y0:\n" ++
  "  sd zero, 8(s3); li t0, 1; sd t0, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_legacy_eip155_y1:\n" ++
  "  li t0, 1; sd t0, 8(s3); sd t0, 120(s3)\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s3, 80\n" ++
  "  jal ra, tx_signing_hash_legacy_eip155\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_scalars\n" ++
  ".Ltps_t1:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip2930_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 8; li a3, 1; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t2:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip1559_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 9; li a3, 2; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t3:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip4844_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 11; li a3, 3; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_t4:\n" ++
  "  mv a0, s6; mv a1, s7; addi a2, s3, 8; addi a3, s3, 16; addi a4, s3, 48\n" ++
  "  jal ra, tx_eip7702_extract_signature\n" ++
  "  bnez a0, .Ltps_sig_fail\n" ++
  "  mv a0, s6; mv a1, s7; li a2, 10; li a3, 4; addi a4, s3, 80\n" ++
  "  jal ra, tx_signing_hash\n" ++
  "  bnez a0, .Ltps_hash_fail\n" ++
  "  j .Ltps_validate_y\n" ++
  ".Ltps_validate_y:\n" ++
  "  ld t0, 8(s3)\n" ++
  "  li t1, 1\n" ++
  "  bgtu t0, t1, .Ltps_bad_y\n" ++
  ".Ltps_validate_scalars:\n" ++
  "  addi a0, s3, 16; jal ra, u256_is_zero\n" ++
  "  bnez a0, .Ltps_r_zero\n" ++
  "  addi a0, s3, 48; jal ra, u256_is_zero\n" ++
  "  bnez a0, .Ltps_s_zero\n" ++
  "  addi a0, s3, 16; la a1, tps_secp256k1_n; la a2, tps_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, tps_cmp; ld t1, 0(t0)\n" ++
  "  beqz t1, .Ltps_r_order\n" ++
  "  la a0, tps_secp256k1_half_n; addi a1, s3, 48; la a2, tps_cmp\n" ++
  "  jal ra, u256_lt_be\n" ++
  "  la t0, tps_cmp; ld t1, 0(t0)\n" ++
  "  bnez t1, .Ltps_s_high\n" ++
  "  li a0, 0\n" ++
  "  j .Ltps_ret\n" ++
  ".Ltps_type_fail:\n" ++
  "  li a0, 1; j .Ltps_ret\n" ++
  ".Ltps_inner_oob:\n" ++
  "  li a0, 2; j .Ltps_ret\n" ++
  ".Ltps_sig_fail:\n" ++
  "  li a0, 10; j .Ltps_ret\n" ++
  ".Ltps_hash_fail:\n" ++
  "  li a0, 20; j .Ltps_ret\n" ++
  ".Ltps_bad_v:\n" ++
  "  li a0, 30; j .Ltps_ret\n" ++
  ".Ltps_bad_y:\n" ++
  "  li a0, 31; j .Ltps_ret\n" ++
  ".Ltps_r_zero:\n" ++
  "  li a0, 40; j .Ltps_ret\n" ++
  ".Ltps_s_zero:\n" ++
  "  li a0, 41; j .Ltps_ret\n" ++
  ".Ltps_r_order:\n" ++
  "  li a0, 42; j .Ltps_ret\n" ++
  ".Ltps_s_high:\n" ++
  "  li a0, 43\n" ++
  ".Ltps_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp)\n" ++
  "  ld s4, 40(sp); ld s5, 48(sp); ld s6, 56(sp); ld s7, 64(sp); ld s8, 72(sp)\n" ++
  "  addi sp, sp, 80\n" ++
  "  ret"


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
def txPubkeyEcrecoverStageMaterialFunction : String :=
  "tx_pubkey_ecrecover_stage_material:\n" ++
  "  addi sp, sp, -32\n" ++
  "  sd s0,  0(sp); sd s1,  8(sp); sd s2, 16(sp); sd s3, 24(sp)\n" ++
  "  mv s0, a0                   # material ptr\n" ++
  "  mv s1, a1                   # staging ptr\n" ++
  "  ld s2, 8(s0)                # recid\n" ++
  "  li t0, 1\n" ++
  "  bgtu s2, t0, .Ltpes_bad_recid\n" ++
  "  # message hash = material.signing_hash\n" ++
  "  addi t0, s0, 80\n" ++
  "  mv t1, s1\n" ++
  "  li t2, 4\n" ++
  ".Ltpes_copy_hash:\n" ++
  "  ld t3, 0(t0); sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltpes_copy_hash\n" ++
  "  # signature = r || s\n" ++
  "  addi t0, s0, 16\n" ++
  "  addi t1, s1, 32\n" ++
  "  li t2, 8\n" ++
  ".Ltpes_copy_sig:\n" ++
  "  ld t3, 0(t0); sd t3, 0(t1)\n" ++
  "  addi t0, t0, 8; addi t1, t1, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltpes_copy_sig\n" ++
  "  sd s2, 96(s1)\n" ++
  "  addi t1, s1, 104\n" ++
  "  li t2, 8\n" ++
  ".Ltpes_zero_pubkey:\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltpes_zero_pubkey\n" ++
  "  li a0, 0\n" ++
  "  j .Ltpes_ret\n" ++
  ".Ltpes_bad_recid:\n" ++
  "  li a0, 1\n" ++
  ".Ltpes_ret:\n" ++
  "  ld s0,  0(sp); ld s1,  8(sp); ld s2, 16(sp); ld s3, 24(sp)\n" ++
  "  addi sp, sp, 32\n" ++
  "  ret"

/-! ## tx_pubkey_recover_raw

    Callable recovered-key helper surface. Mirrors execution-specs Amsterdam
    `recover_transaction_public_key`: build the signature material, stage it into
    the `zkvm_secp256k1_ecrecover(msg, sig, recid, output)` ABI, then (eventually)
    run secp256k1 recovery to produce the 64-byte public key. This child only
    wires the call surface and scratch layout; the software recovery backend is
    not implemented yet, so success paths terminate at status 50 rather than
    pretending recovery succeeded. The safe-fail accelerator wrapper is
    deliberately NOT used, and no stateless `public_keys` comparison happens here.

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
      +136  staged ecrecover ABI block (168 bytes; msg hash 32 || sig 64 ||
            recid word 8 || reserved pubkey buffer 64)

    Status:
      0  reserved for future success (real recovery lands later)
      10 signature material failed (material status stored at scratch +0)
      20 ecrecover ABI staging failed
      50 software secp256k1 recovery backend not implemented yet

    On status 50 the recovered-pubkey output buffer is zeroed so callers never
    observe stale bytes from a non-recovery run. -/
def txPubkeyRecoverRawFunction : String :=
  "tx_pubkey_recover_raw:\n" ++
  "  addi sp, sp, -48\n" ++
  "  sd ra,  0(sp)\n" ++
  "  sd s0,  8(sp); sd s1, 16(sp); sd s2, 24(sp); sd s3, 32(sp); sd s4, 40(sp)\n" ++
  "  mv s0, a0                   # tx ptr\n" ++
  "  mv s1, a1                   # tx len\n" ++
  "  mv s2, a2                   # chain_id\n" ++
  "  mv s3, a3                   # recovered pubkey out\n" ++
  "  mv s4, a4                   # scratch ptr\n" ++
  "  # build signature material into scratch+8\n" ++
  "  mv a0, s0; mv a1, s1; mv a2, s2; addi a3, s4, 8\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  sd a0, 0(s4)                # record material status in side slot\n" ++
  "  beqz a0, .Ltprr_material_ok\n" ++
  "  li a0, 10\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_material_ok:\n" ++
  "  # stage material into ecrecover ABI at scratch+136\n" ++
  "  addi a0, s4, 8; addi a1, s4, 136\n" ++
  "  jal ra, tx_pubkey_ecrecover_stage_material\n" ++
  "  beqz a0, .Ltprr_stage_ok\n" ++
  "  li a0, 20\n" ++
  "  j .Ltprr_ret\n" ++
  ".Ltprr_stage_ok:\n" ++
  "  # software secp256k1 recovery backend not implemented yet; zero the\n" ++
  "  # 64-byte output buffer so no stale bytes leak, then report status 50.\n" ++
  "  mv t1, s3\n" ++
  "  li t2, 8\n" ++
  ".Ltprr_zero_out:\n" ++
  "  sd zero, 0(t1)\n" ++
  "  addi t1, t1, 8; addi t2, t2, -1\n" ++
  "  bnez t2, .Ltprr_zero_out\n" ++
  "  li a0, 50\n" ++
  ".Ltprr_ret:\n" ++
  "  ld ra,  0(sp)\n" ++
  "  ld s0,  8(sp); ld s1, 16(sp); ld s2, 24(sp); ld s3, 32(sp); ld s4, 40(sp)\n" ++
  "  addi sp, sp, 48\n" ++
  "  ret"

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
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  li a3, 0xa0010008           # material out\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  li s0, 0xa0010000\n" ++
  "  sd a0, 0(s0)                # material status\n" ++
  "  bnez a0, .Ltpes_probe_done\n" ++
  "  addi a0, s0, 8              # material ptr\n" ++
  "  addi a1, s0, 144            # staged ABI ptr\n" ++
  "  jal ra, tx_pubkey_ecrecover_stage_material\n" ++
  "  sd a0, 136(s0)              # stage status\n" ++
  "  j .Ltpes_probe_done\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
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
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  li a3, 0xa0010008           # material out\n" ++
  "  jal ra, tx_pubkey_signature_material\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)\n" ++
  "  j .Ltps_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
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
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xfe\n" ++
  "  .byte 0xba,0xae,0xdc,0xe6,0xaf,0x48,0xa0,0x3b\n" ++
  "  .byte 0xbf,0xd2,0x5e,0x8c,0xd0,0x36,0x41,0x41\n" ++
  "tps_secp256k1_half_n:\n" ++
  "  .byte 0x7f,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff\n" ++
  "  .byte 0x5d,0x57,0x6e,0x73,0x57,0xa4,0x50,0x1d\n" ++
  "  .byte 0xdf,0xe9,0x2f,0x46,0x68,0x1b,0x20,0xa0\n" ++
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
  "tsh_buf:\n  .zero 8192\n" ++
  "tsh_trunc_len:\n  .zero 8\n" ++
  "rltn_offset_lo:\n  .zero 8\n" ++
  "rltn_length_lo:\n  .zero 8\n" ++
  "rltn_offset_hi:\n  .zero 8\n" ++
  "rltn_length_hi:\n  .zero 8\n" ++
  "rltn_prefix_len:\n  .zero 8\n" ++
  "t155_buf:\n  .zero 8192\n" ++
  "t155_offset_lo:\n  .zero 8\n" ++
  "t155_length_lo:\n  .zero 8\n" ++
  "t155_offset_hi:\n  .zero 8\n" ++
  "t155_length_hi:\n  .zero 8\n" ++
  "t155_chain_be:\n  .zero 8\n" ++
  "t155_chain_enc:\n  .zero 9\n" ++
  ".balign 8\n" ++
  "t155_prefix_len:\n  .zero 8"

def ziskTxPubkeyEcrecoverStageMaterialProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeyEcrecoverStageMaterialPrologue
  dataAsm     := ziskTxPubkeySignatureMaterialDataSection
}

def ziskTxPubkeySignatureMaterialProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeySignatureMaterialPrologue
  dataAsm     := ziskTxPubkeySignatureMaterialDataSection
}

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
  "  li sp, 0xa0050000\n" ++
  "  li a5, 0x40000000\n" ++
  "  ld a1, 8(a5)                # tx_len\n" ++
  "  ld a2, 16(a5)               # chain_id\n" ++
  "  addi a0, a5, 24             # tx ptr\n" ++
  "  la a3, tprr_pubkey_out      # recovered pubkey out (64 bytes)\n" ++
  "  la a4, tprr_scratch         # scratch (>= 304 bytes)\n" ++
  "  jal ra, tx_pubkey_recover_raw\n" ++
  "  li t0, 0xa0010000\n" ++
  "  sd a0, 0(t0)                # helper status\n" ++
  "  la t1, tprr_scratch\n" ++
  "  ld t2, 0(t1)\n" ++
  "  sd t2, 8(t0)                # material status side slot\n" ++
  "  j .Ltprrs_pdone\n" ++
  txTypeDispatchFunction ++ "\n" ++
  rlpListNthItemFunction ++ "\n" ++
  rlpEncodeUintBeFunction ++ "\n" ++
  rlpEncodeListPrefixFunction ++ "\n" ++
  rlpListTruncateToNFieldsFunction ++ "\n" ++
  zkvmKeccak256Function ++ "\n" ++
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
  txPubkeyRecoverRawFunction ++ "\n" ++
  ".Ltprrs_pdone:"

def ziskTxPubkeyRecoverRawStatusDataSection : String :=
  ziskTxPubkeySignatureMaterialDataSection ++ "\n" ++
  "tprr_pubkey_out:\n  .zero 64\n" ++
  "tprr_scratch:\n  .zero 312"

def ziskTxPubkeyRecoverRawStatusProbeUnit : BuildUnit := {
  body        := NOP
  prologueAsm := ziskTxPubkeyRecoverRawStatusPrologue
  dataAsm     := ziskTxPubkeyRecoverRawStatusDataSection
}

end EvmAsm.Codegen
